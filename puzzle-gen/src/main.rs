use std::ops::ControlFlow;

use anyhow::{Context, anyhow};
use clap::{Parser, ValueEnum};
use log::{Level, debug, info, trace};
use rand::SeedableRng;
use rig::client::Nothing;
use rig::providers::{gemini, ollama};
use smtlib::Storage;
use smtlib::backend::cvc5_binary::Cvc5Binary;

#[macro_use]
mod macros;
mod concrete_theories;
mod llm;
mod pprint;
mod solvers;
mod theories;

use crate::concrete_theories::workplace::{WorkplaceGenerator, WorkplaceQueryGenerator};
use crate::llm::RendererAgent;
use crate::pprint::{PrettyFormula, PrettyInstance};
use crate::solvers::{Backend, QueryResult, SmtBackend};
use crate::theories::{
    AblationStrategy, AllAtOnceAblation, Instance, ModelGenerator, QueryGenerator,
    StochasticAblation,
};

#[derive(Copy, Clone, Debug, ValueEnum)]
enum AblationKind {
    /// Drop every implicit-by-default axiom in a single step.
    AllAtOnce,
    /// Drop one randomly-chosen implicit-by-default axiom per step.
    Stochastic,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum LLMProvider {
    /// Google Gemini backend (gemini-flash-3.0-preview by default)
    Gemini,
    /// Ollama backend (gemma4 by default)
    Ollama,
}

/// Provider-agnostic wrapper for RendererAgent
#[derive(Clone)]
enum AnyRendererAgent {
    Gemini(RendererAgent<gemini::completion::CompletionModel>),
    Ollama(RendererAgent<ollama::CompletionModel>),
}

impl TryFrom<LLMProvider> for AnyRendererAgent {
    type Error = anyhow::Error;

    fn try_from(value: LLMProvider) -> Result<Self, Self::Error> {
        match value {
            LLMProvider::Gemini => std::env::var("GEMINI_API_KEY")
                .context("environment variable GEMINI_API_KEY not set")
                .and_then(|api_key| {
                    let client = gemini::Client::new(api_key)
                        .context("couldn't construct Gemini API client")?;
                    Ok(Self::Gemini(RendererAgent::new(
                        client,
                        gemini::completion::GEMINI_3_FLASH_PREVIEW,
                    )))
                }),
            LLMProvider::Ollama => ollama::Client::new(Nothing)
                .context("couldn't construct Ollama API client")
                .map(|client| Self::Ollama(RendererAgent::new(client, "gemma4:latest"))),
        }
    }
}

impl AnyRendererAgent {
    async fn render<'t>(&self, instance: &Instance<'t>) -> anyhow::Result<String> {
        match self {
            AnyRendererAgent::Gemini(agent) => agent.render(instance).await,
            AnyRendererAgent::Ollama(agent) => agent.render(instance).await,
        }
    }
}

#[derive(Parser, Debug)]
#[command(version)]
struct Args {
    /// Log level (overrides RUST_LOG when set)
    #[arg(long)]
    log_level: Option<Level>,

    /// Ablation strategy.
    #[arg(long, value_enum, default_value_t = AblationKind::Stochastic)]
    ablation: AblationKind,

    /// Number of departments in the generated hierarchy.
    #[arg(long, default_value_t = 3)]
    n_departments: usize,

    /// Maximum depth of the hierarchy tree (root = depth 0).
    #[arg(long, default_value_t = 3)]
    max_depth: usize,

    /// Mean span of control (Poisson rate) for direct reports.
    #[arg(long, default_value_t = 2.0)]
    span_of_control: f64,

    /// PRNG seed.
    #[arg(long, default_value_t = 0)]
    seed: u64,

    /// Path to the cvc5 binary.
    #[arg(long, default_value = "cvc5")]
    cvc5: String,

    /// LLM backend to use for natural language rendering.
    #[arg(long, short, value_enum, default_value = "ollama")]
    llm_provider: LLMProvider,
}

fn logger_setup(level: Option<Level>) -> anyhow::Result<()> {
    let mut builder = env_logger::Builder::new();
    // RUST_LOG as base layer
    builder.parse_default_env();
    // --log-level overrides RUST_LOG; if neither is set, default to Info
    match level {
        Some(l) => builder.filter_level(l.to_level_filter()),
        None if std::env::var("RUST_LOG").is_err() => builder.filter_level(log::LevelFilter::Info),
        None => &mut builder,
    };
    builder.try_init().context("couldn't initialize logger")
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    logger_setup(args.log_level)?;
    info!("puzzle-gen started");
    debug!("{:?}", &args);

    let mut rng = rand::rngs::StdRng::seed_from_u64(args.seed);

    // 1. Generate a ground-truth model.
    let mut model_gen = WorkplaceGenerator::try_new(
        rand::rngs::StdRng::seed_from_u64(args.seed.wrapping_add(1)),
        args.span_of_control,
        args.max_depth,
        args.n_departments,
    )
    .context("invalid Poisson distribution")?;
    let model = model_gen.generate();
    info!(
        "generated model: {} employees, {} departments",
        model.domain().values().map(|v| v.len()).sum::<usize>(),
        args.n_departments,
    );

    // 2. Sample a query against the model.
    let mut query_gen =
        WorkplaceQueryGenerator::new(rand::rngs::StdRng::seed_from_u64(args.seed.wrapping_add(2)));
    let query = query_gen.generate(&model);

    // 3. Materialise the model as an Instance with all axioms active.
    let mut instance = Instance::from_ground_model(model);
    trace!("initialized instance");
    info!(
        "query: {}",
        PrettyFormula {
            formula: &query,
            instance: &instance
        }
    );

    // 4. Set up the SMT backend.
    debug!("using cvc5 binary at `{}`", args.cvc5);
    let storage = Storage::new();
    let cvc5 = Cvc5Binary::new(&args.cvc5)
        .with_context(|| format!("failed to spawn cvc5 at `{}`", args.cvc5))?;
    let mut backend = SmtBackend::new(&storage, cvc5).context("failed to construct SMT backend")?;
    trace!("initialized backend");

    // 5. Sanity-check: with the full theory the query must be uniquely decided.
    backend
        .load_instance(&instance)
        .context("loading initial instance")?;
    let initial = backend
        .check_entailment(&query)
        .context("initial entailment check")?;
    info!("initial entailment status: {:?}", initial);
    match initial {
        QueryResult::Entailed | QueryResult::Refuted => {}
        QueryResult::Undetermined => {
            return Err(anyhow!(
                "ground theory does not uniquely decide the sampled query — \
                 cannot generate a puzzle from this model/query pair"
            ));
        }
    }

    // 6. Ablation loop. Each step deactivates more axioms; we stop the moment
    //    the query becomes underdetermined (or wrongly decided) and keep that
    //    *first bad* instance state as the puzzle — the solver can only recover
    //    the correct answer by invoking the oracle to supply the missing axiom.
    let mut strategy: Box<dyn AblationStrategy> = match args.ablation {
        AblationKind::AllAtOnce => Box::new(AllAtOnceAblation),
        AblationKind::Stochastic => Box::new(StochasticAblation::new(instance.theory(), &mut rng)),
    };

    let mut first_bad_status: Option<QueryResult> = None;
    let mut step = 0usize;
    loop {
        let cf = strategy.ablate(&mut instance);
        step += 1;
        backend
            .load_instance(&instance)
            .with_context(|| format!("reloading instance after ablation step {step}"))?;
        let status = backend
            .check_entailment(&query)
            .with_context(|| format!("entailment check at step {step}"))?;

        if status != initial {
            // Removing this axiom changed the answer — keep this axiom set as
            // the puzzle; the oracle must recover the missing axiom to solve it.
            info!(
                "step {step}: answer flipped ({:?} → {:?}); keeping this axiom set as puzzle",
                initial, status
            );
            first_bad_status = Some(status);
            break;
        }

        debug!("step {step}: answer still {:?}", status);

        if cf.is_break() {
            // Strategy exhausted without ever flipping — no implicit axiom is
            // load-bearing, so there is nothing for the oracle to recover.
            break;
        }
    }

    let puzzle_status = first_bad_status.ok_or_else(|| {
        anyhow!(
            "ablation never changed the answer — no implicit axiom is load-bearing; \
             cannot generate a puzzle that exercises the oracle"
        )
    })?;

    info!(
        "puzzle ready: {} axioms remain active, ground answer without oracle = {:?}",
        instance.active_axioms().len(),
        puzzle_status,
    );

    let pretty = format!(
        "{}",
        PrettyInstance {
            instance: &instance
        }
    );
    for line in pretty.lines() {
        info!("{line}");
    }

    let renderer = AnyRendererAgent::try_from(args.llm_provider)?;
    let nl_story = renderer.render(&instance).await?;
    for line in nl_story.lines() {
        info!("{line}");
    }

    info!("exiting");
    Ok(())
}

impl<'t> AblationStrategy for Box<dyn AblationStrategy> {
    fn ablate(&mut self, inst: &mut Instance) -> ControlFlow<()> {
        (**self).ablate(inst)
    }
}
