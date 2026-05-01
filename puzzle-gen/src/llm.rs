//! Interface for querying LLMs

use anyhow::Context;
use rig::{
    agent::Agent,
    client::CompletionClient,
    completion::{CompletionModel, Prompt},
};

use crate::pprint::PrettyInstance;
use crate::theories::Instance;

const RENDERER_SYSTEM_PROMPT: &'static str = "
    You are a logic puzzle expert. You are able to construct a natural language
    logic puzzle from a formal, first-order-logic specification of a theory (set
    of axioms), a set of facts, and a query. The puzzle should have a natural
    langauge preamble describing the setup of the puzzle, including all listed
    facts. All axioms should be listed in natural language. The query should be
    the last sentence of the puzzle description and should be written as a
    question.

    Write only the puzzle; do not ask follow up questions.
";

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
    pub fn new<C>(client: C, agent: impl Into<String>) -> Self
    where
        C: CompletionClient<CompletionModel = M>,
    {
        let agent = client
            .agent(agent)
            .preamble(RENDERER_SYSTEM_PROMPT)
            .temperature(0.0)
            .build();
        Self { agent }
    }

    /// Render the instance as a logic puzzle.
    pub async fn render<'t>(&self, instance: &Instance<'t>) -> anyhow::Result<String> {
        let mut buf = String::new();
        if let Some(preamble) = instance.preamble() {
            buf.extend(preamble.lines());
            buf.push('\n');
        }
        let pretty = PrettyInstance { instance };
        buf.push_str(pretty.to_string().as_ref());
        self.agent.prompt(buf).await.context("error prompting LLM")
    }
}
