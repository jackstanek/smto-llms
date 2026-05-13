//! Interface for querying LLMs.
//!
//! `RendererAgent<M>` is the generic rig-backed agent that turns the
//! template renderer's structured output into natural-language flavour
//! text. The rest of the program talks to it through the
//! `LlmRenderer` trait object so the choice of backend (OpenAI,
//! Anthropic, local Ollama, …) stays a CLI concern.

use async_trait::async_trait;
use clap::ValueEnum;
use rig::{
    agent::Agent,
    client::{ModelListingClient, Nothing, ProviderClient},
    completion::{CompletionModel, Prompt, PromptError},
    model::ModelListingError,
    prelude::CompletionClient,
    providers::{gemini, ollama},
};
use thiserror::Error;

/// Main error type for LLM-related errors.
#[derive(Debug, Error)]
pub enum LlmError {
    #[error("prompt error: {0}")]
    PromptError(#[from] PromptError),
    #[error("model listing error: {0}")]
    ModelListingError(#[from] ModelListingError),
    #[error("HTTP error: {0}")]
    HttpError(#[from] rig::http_client::Error),
    #[error("no such model (available models: {joined})", joined = avail_models.join(", "))]
    NoSuchModel {
        /// Available models from the selected provider
        avail_models: Vec<String>,
    },
}

const RENDERER_SYSTEM_PROMPT: &str = "
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

/// Valid model name for some provider.
pub struct ValidModelName {
    name: String,
}

impl ValidModelName {
    /// Validate a model name against some provider, returning a
    /// `ValidModelName` if it is available, or a list of available models if it
    /// is not.
    pub async fn validate<C>(client: &C, name: impl Into<String>) -> Result<Self, LlmError>
    where
        C: ModelListingClient,
    {
        let models = client.list_models().await?;
        let name = name.into();
        // Check if the model is available before constructing
        if models.iter().any(|m| m.id.as_str() == name.as_str()) {
            Ok(Self { name })
        } else {
            let avail_models = models.into_iter().map(|m| m.id).collect();
            Err(LlmError::NoSuchModel { avail_models })
        }
    }
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
    pub fn new<C>(client: C, model_name: ValidModelName) -> Self
    where
        C: CompletionClient<CompletionModel = M>,
    {
        let agent = client
            .agent(model_name.name)
            .preamble(RENDERER_SYSTEM_PROMPT)
            .temperature(0.0)
            .build();
        Self { agent }
    }
}

#[async_trait]
pub trait LlmRenderer {
    async fn render(&self, input: &str) -> Result<String, LlmError>;
}

#[async_trait]
impl<M> LlmRenderer for RendererAgent<M>
where
    M: CompletionModel + Send + Sync + 'static,
{
    async fn render(&self, input: &str) -> Result<String, LlmError> {
        Ok(self.agent.prompt(input).await?)
    }
}

/// LLM backend selector. New providers are added as variants here and in
/// `build_renderer`; the rest of the program only sees `dyn LlmRenderer`.
#[derive(Copy, Clone, Debug, ValueEnum)]
pub enum Provider {
    /// Gemini. Reads `GEMINI_API_KEY`.
    Gemini,
    /// Ollama, for local models. Defaults to `http://localhost:11434`;
    /// override with `--ollama-url` or `OLLAMA_API_BASE_URL`.
    Ollama,
}

impl Provider {
    /// Build a renderer for this provider. Returns a trait object so
    /// callers don't have to know which `CompletionModel` was selected.
    pub async fn build_renderer(
        self,
        model_name: impl Into<String>,
        ollama_url: Option<&str>,
    ) -> Result<Box<dyn LlmRenderer>, LlmError> {
        Ok(match self {
            Provider::Gemini => {
                let client = gemini::Client::from_env();
                let model_name = ValidModelName::validate(&client, model_name).await?;
                Box::new(RendererAgent::new(client, model_name)) as Box<dyn LlmRenderer>
            }
            Provider::Ollama => {
                let mut builder = ollama::Client::builder().api_key(Nothing);
                if let Some(url) = ollama_url {
                    builder = builder.base_url(url);
                }
                let client = builder.build().map_err(LlmError::from)?;
                let model_name = ValidModelName::validate(&client, model_name).await?;
                Box::new(RendererAgent::new(client, model_name)) as Box<dyn LlmRenderer>
            }
        })
    }
}
