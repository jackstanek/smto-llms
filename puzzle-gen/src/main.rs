use std::ops::ControlFlow;

use anyhow::{Context, anyhow};
use clap::{Parser, ValueEnum};
use log::{Level, debug, info, warn};
use rand::SeedableRng;
use smtlib::Storage;
use smtlib::backend::cvc5_binary::Cvc5Binary;

#[macro_use]
mod macros;
mod concrete_theories;
mod solvers;
mod theories;

use crate::concrete_theories::workplace::{WorkplaceGenerator, WorkplaceQueryGenerator};
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

#[derive(Parser, Debug)]
#[command(version)]
pub struct Args {
    /// Log level
    #[arg(long, default_value_t = Level::Info)]
    log_level: Level,

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
}

fn logger_setup(level: &Level) -> anyhow::Result<()> {
    env_logger::builder()
        .filter_level(level.to_level_filter())
        .try_init()
        .context("couldn't initialize logger")
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    logger_setup(&args.log_level)?;
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
    .map_err(|e| anyhow!("invalid Poisson distribution: {e}"))?;
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
    debug!("query: {:?}", &query);

    // 3. Materialise the model as an Instance with all axioms active.
    let mut instance = Instance::from_ground_model(model);

    // 4. Set up the SMT backend.
    let storage = Storage::new();
    let cvc5 = Cvc5Binary::new(&args.cvc5)
        .with_context(|| format!("failed to spawn cvc5 at `{}`", args.cvc5))?;
    let mut backend = SmtBackend::new(&storage, cvc5).context("failed to construct SMT backend")?;

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
    //    the query becomes underdetermined (or, defensively, inconsistent) and
    //    return the *previous* instance state as the puzzle.
    let mut last_good = instance.active_axioms().clone();
    let mut last_good_status = initial;
    let mut strategy: Box<dyn AblationStrategy> = match args.ablation {
        AblationKind::AllAtOnce => Box::new(AllAtOnceAblation),
        AblationKind::Stochastic => Box::new(StochasticAblation::new(instance.theory(), &mut rng)),
    };

    let mut step = 0usize;
    loop {
        let cf = strategy.ablate(&mut instance);
        step += 1;
        backend
            .load_instance(&instance)
            .with_context(|| format!("reloading instance after ablation step {step}"))?;
        match backend
            .check_entailment(&query)
            .with_context(|| format!("entailment check at step {step}"))?
        {
            status @ (QueryResult::Entailed | QueryResult::Refuted) => {
                debug!("step {step}: still uniquely decided ({:?})", status);
                last_good = instance.active_axioms().clone();
                last_good_status = status;
            }
            QueryResult::Undetermined => {
                info!("step {step}: query became underdetermined; reverting to previous axiom set");
                break;
            }
        }
        if cf.is_break() {
            // Strategy is exhausted but the query is still uniquely decided —
            // the implicit axioms aren't load-bearing for this query.
            warn!(
                "ablation strategy exhausted with query still uniquely decided ({:?}); \
                 puzzle does not exercise the oracle",
                last_good_status
            );
            break;
        }
    }
    instance.set_active_axioms(last_good);

    info!(
        "puzzle ready: {} axioms remain active, ground answer = {:?}",
        instance.active_axioms().len(),
        last_good_status,
    );

    info!("exiting");
    Ok(())
}

impl<'t> AblationStrategy for Box<dyn AblationStrategy> {
    fn ablate(&mut self, inst: &mut Instance) -> ControlFlow<()> {
        (**self).ablate(inst)
    }
}
