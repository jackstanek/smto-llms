//! Interface for querying LLMs.
//!
//! `RendererAgent<M>` is the generic rig-backed agent that turns the
//! template renderer's structured output into natural-language flavour
//! text. The rest of the program talks to it through the
//! `LlmRenderer` trait object so the choice of backend (OpenAI,
//! Anthropic, local Ollama, …) stays a CLI concern.

use anyhow::{Context, anyhow};
use async_trait::async_trait;
use clap::ValueEnum;
use rig::{
    agent::Agent,
    client::{Nothing, ProviderClient},
    completion::{CompletionModel, Prompt},
    prelude::CompletionClient,
    providers::{anthropic, gemini, ollama, openai},
};

const RENDERER_SYSTEM_PROMPT: &'static str = "

    You are a prose stylist for logic puzzles. You will be given a logic
    puzzle that has already been rendered into plain English from a formal
    specification: a short preamble, a list of facts, a list of rules, and
    a yes-or-no query at the end.

    Your job is to rewrite the puzzle as fluent, engaging flavour text that
    sets the scene and gives the reader context for the situation — for
    example, framing a workplace puzzle as a story about a real company.
    Keep the prose natural and readable; you may reorder sentences,
    combine them, and add neutral connective tissue (\"meanwhile\",
    \"also\", names of rooms or projects) so the text reads like a story
    rather than a bullet list.

    Hard constraints:
    - Preserve every fact and rule exactly as given. Do not add, remove,
      strengthen, or weaken any of them.
    - Do not introduce new people, roles, relationships, or constraints
      that were not in the input.
    - Keep the query intact as a yes-or-no question, and place it as the
      final sentence.
    - Output only the rewritten puzzle. No preamble, commentary, or
      follow-up questions. Do not answer the puzzle yourself.
";

/// Provider-agnostic rendering interface. Each backend (`RendererAgent<M>`
/// over some concrete rig `CompletionModel`) implements this, and `main`
/// holds a `Box<dyn LlmRenderer>` chosen from the `--llm-provider` flag.
#[async_trait]
pub trait LlmRenderer: Send + Sync {
    async fn render(&self, input: &str) -> anyhow::Result<String>;
}

#[derive(Clone)]
pub struct RendererAgent<M>
where
    M: CompletionModel,
{
    agent: Agent<M>,
}

impl<M> RendererAgent<M>
where
    M: CompletionModel + 'static,
{
    /// Construct a new renderer agent which constructs logic puzzles from the
    /// given instances.
    pub fn new<C>(client: C, model_name: impl Into<String>) -> Self
    where
        C: CompletionClient<CompletionModel = M>,
    {
        let agent = client
            .agent(model_name)
            .preamble(RENDERER_SYSTEM_PROMPT)
            .temperature(0.0)
            .build();
        Self { agent }
    }
}

#[async_trait]
impl<M> LlmRenderer for RendererAgent<M>
where
    M: CompletionModel + Send + Sync + 'static,
{
    async fn render(&self, input: &str) -> anyhow::Result<String> {
        self.agent
            .prompt(input)
            .await
            .context("couldn't access LLM agent")
    }
}

/// LLM backend selector. New providers are added as variants here and in
/// `build_renderer`; the rest of the program only sees `dyn LlmRenderer`.
#[derive(Copy, Clone, Debug, ValueEnum)]
pub enum Provider {
    /// OpenAI (Responses API). Reads `OPENAI_API_KEY`.
    Openai,
    /// Anthropic. Reads `ANTHROPIC_API_KEY`.
    Anthropic,
    /// Gemini. Reads `GEMINI_API_KEY`.
    Gemini,
    /// Ollama, for local models. Defaults to `http://localhost:11434`;
    /// override with `--ollama-url` or `OLLAMA_API_BASE_URL`.
    Ollama,
}

impl Provider {
    /// Build a renderer for this provider. Returns a trait object so
    /// callers don't have to know which `CompletionModel` was selected.
    pub fn build_renderer(
        self,
        model_name: impl Into<String>,
        ollama_url: Option<&str>,
    ) -> anyhow::Result<Box<dyn LlmRenderer>> {
        let model_name = model_name.into();
        Ok(match self {
            Provider::Openai => {
                Box::new(RendererAgent::new(openai::Client::from_env(), model_name))
            }
            Provider::Anthropic => Box::new(RendererAgent::new(
                anthropic::Client::from_env(),
                model_name,
            )),
            Provider::Gemini => {
                Box::new(RendererAgent::new(gemini::Client::from_env(), model_name))
            }
            Provider::Ollama => {
                let mut builder = ollama::Client::builder().api_key(Nothing);
                if let Some(url) = ollama_url {
                    builder = builder.base_url(url);
                }
                let client = builder
                    .build()
                    .map_err(|e| anyhow!("failed to build Ollama client: {e}"))?;
                Box::new(RendererAgent::new(client, model_name))
            }
        })
    }
}
