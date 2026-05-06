//! Template-based renderer for theories.
//!
//! Combines per-symbol natural-language templates (declared on each
//! `SymbolDecl` via `nl_template`) with a per-instance pretty-name map
//! (built by a `NameInitializer`) to produce prose facts, rules, and the
//! query. The skeleton (preamble, fact list, rule list, query) is rendered
//! through an Askama template; only the leaves are formatted here.

use anyhow::{Context, anyhow};
use askama::Template;

use crate::rendering::{NameInitializer, NameMap, Renderer};
use crate::theories::{Atom, AxiomBody, Formula, Instance, Term, Theory};

#[derive(Template)]
#[template(path = "theory.jinja2")]
struct TheoryTemplate {
    preamble: String,
    facts: Vec<String>,
    rules: Vec<String>,
    query: String,
}

/// Template renderer for concrete theories. Uses the symbol-level
/// `nl_template` strings together with a per-instance `NameMap` (built by
/// the `NameInitializer`) to render facts and the query as prose.
pub struct TemplateRenderer<I> {
    initializer: I,
}

impl<I> TemplateRenderer<I>
where
    I: NameInitializer,
{
    pub fn new(initializer: I) -> Self {
        Self { initializer }
    }
}

impl<I> Renderer for TemplateRenderer<I>
where
    I: NameInitializer,
{
    type Error = anyhow::Error;

    async fn render(
        &self,
        query: &Formula,
        instance: &Instance<'_>,
    ) -> Result<String, Self::Error> {
        let mut names = NameMap::new();
        self.initializer.init_map(instance, &mut names);
        let theory = instance.theory();

        let facts = instance
            .facts()
            .iter()
            .map(|atom| render_atom(theory, &names, atom))
            .collect::<Result<Vec<_>, _>>()
            .context("rendering facts")?;

        let rules = instance
            .active_axioms()
            .iter()
            .map(|id| theory.axiom(*id).natural_language().to_string())
            .collect();

        let query = render_formula(theory, &names, query).context("rendering query")?;

        TheoryTemplate {
            preamble: instance.preamble().unwrap_or_default().to_string(),
            facts,
            rules,
            query,
        }
        .render()
        .context("couldn't render theory template")
    }
}

/// Render a ground atom as prose using the symbol's `nl_template`.
fn render_atom(theory: &Theory, names: &NameMap, atom: &Atom) -> anyhow::Result<String> {
    match atom {
        Atom::Predicate { symbol, args } => {
            let decl = theory.symbol(*symbol);
            let template = decl.nl_template().ok_or_else(|| {
                anyhow!("predicate `{}` has no nl_template", decl.name())
            })?;
            let arg_names = args
                .iter()
                .map(|t| resolve_term(names, t))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(fill_template(template, &arg_names, None))
        }
        Atom::Eq(lhs, rhs) => match (lhs, rhs) {
            (Term::App { symbol, args }, value) => {
                let decl = theory.symbol(*symbol);
                let template = decl.nl_template().ok_or_else(|| {
                    anyhow!("function `{}` has no nl_template", decl.name())
                })?;
                let arg_names = args
                    .iter()
                    .map(|t| resolve_term(names, t))
                    .collect::<Result<Vec<_>, _>>()?;
                let ret = resolve_term(names, value)?;
                Ok(fill_template(template, &arg_names, Some(&ret)))
            }
            (a, b) => Ok(format!(
                "{} is {}",
                resolve_term(names, a)?,
                resolve_term(names, b)?
            )),
        },
        Atom::Neq(a, b) => Ok(format!(
            "{} is not {}",
            resolve_term(names, a)?,
            resolve_term(names, b)?
        )),
    }
}

/// Render a formula. The current query generators only emit ground atoms,
/// but we support the basic boolean connectives so this stays useful as
/// the IR grows.
fn render_formula(theory: &Theory, names: &NameMap, formula: &Formula) -> anyhow::Result<String> {
    match formula {
        Formula::Atom(atom) => render_atom(theory, names, atom),
        Formula::Not(inner) => Ok(format!(
            "it is not the case that {}",
            render_formula(theory, names, inner)?
        )),
        Formula::And(parts) => Ok(parts
            .iter()
            .map(|f| render_formula(theory, names, f))
            .collect::<Result<Vec<_>, _>>()?
            .join(" and ")),
        Formula::Or(parts) => Ok(parts
            .iter()
            .map(|f| render_formula(theory, names, f))
            .collect::<Result<Vec<_>, _>>()?
            .join(" or ")),
        Formula::Implies(p, q) => Ok(format!(
            "if {} then {}",
            render_formula(theory, names, p)?,
            render_formula(theory, names, q)?
        )),
        Formula::Forall(_, _) | Formula::Exists(_, _) => {
            Err(anyhow!("quantified formulas are not yet supported in prose rendering"))
        }
    }
}

/// Resolve a term to its prose form. Domain constants go through the name
/// map; theory-level constants fall back to their declared name.
fn resolve_term(names: &NameMap, term: &Term) -> anyhow::Result<String> {
    match term {
        Term::DomainConst(c) => names
            .get(c)
            .cloned()
            .ok_or_else(|| anyhow!("no pretty name assigned for domain constant {:?}", c)),
        Term::Var(_) => Err(anyhow!("cannot render free variable in ground prose")),
        Term::Const(_) | Term::App { .. } => Err(anyhow!(
            "non-ground terms are not supported as atom arguments here"
        )),
    }
}

/// Substitute `{0}`, `{1}`, ..., and optionally `{ret}` into a template.
/// Lightweight — the templates are short and authored by us, so a full
/// format-string parser would be overkill.
fn fill_template(template: &str, args: &[String], ret: Option<&str>) -> String {
    let mut out = template.to_string();
    for (i, arg) in args.iter().enumerate() {
        out = out.replace(&format!("{{{i}}}"), arg);
    }
    if let Some(r) = ret {
        out = out.replace("{ret}", r);
    }
    out
}
