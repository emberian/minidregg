//! The shell's one-line law grammar. It renders to the Host's existing `Pred`
//! JSON (`Host/Json.lean` `predicate`) and adds no semantics: every production
//! is one `Pred` constructor over one projected slot.
//!
//! ```text
//! law    := clause (';' clause)* [';']        one clause is itself; more are `all`
//! clause := 'sealed' | 'open'                 any [] | all []
//!         | ('any' | 'all') '[' [clause (',' clause)*] ']'
//!         | 'not' '(' clause ')'
//!         | field ('monotone' | 'writeOnce')
//!         | slot ('==' value | '<=' value | 'in' '{' value (',' value)* '}')
//! field  := 'field' N                         resource/field/N/after
//! slot   := field ['before' | 'after' | 'delta']
//!         | 'pair' A ',' B 'delta'            resource/pair/A/B/delta
//!         | 'subject' | 'verb' | 'cost'       request/*
//!         | 'slot' STRING                     any other projected slot
//! value  := integer | read | write | delegate | install | revoke   (names on `verb` only)
//! ```
//!
//! Verb names are the tags `request/verb` carries
//! (`CredentialAuthorityEntryCodec.verbTag`): read 1, write 2, delegate 3,
//! install 4, revoke 5. `monotone` and `writeOnce` compare the old and new
//! views of one slot; they take only a field's `after` view, because the old
//! and new views of `before` and `delta` coincide and the atom could never
//! refuse. The Host renders a refused clause in this same grammar.
//!
//! There is no `witnessed` clause: Mini admits by re-execution, and with no
//! proof system in admission (decision 10-01) the `witnessed` atom compiles to
//! false, so a law that named it would refuse every write. The grammar refuses
//! the word instead of offering a clause that can never hold.

use serde_json::{json, Value};

const VERBS: [(&str, i64); 5] = [("read", 1), ("write", 2), ("delegate", 3), ("install", 4), ("revoke", 5)];

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Word(String),
    Int(i64),
    Str(String),
    Punct(&'static str),
}

fn tokens(text: &str) -> Result<Vec<Tok>, String> {
    let chars: Vec<char> = text.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        let two: String = chars[i..chars.len().min(i + 2)].iter().collect();
        if two == "==" || two == "<=" {
            out.push(Tok::Punct(if two == "==" { "==" } else { "<=" }));
            i += 2;
            continue;
        }
        if let Some(p) = ["[", "]", "(", ")", "{", "}", ",", ";"].into_iter().find(|p| p.starts_with(c)) {
            out.push(Tok::Punct(p));
            i += 1;
            continue;
        }
        if c == '"' {
            let mut s = String::new();
            i += 1;
            loop {
                match chars.get(i) {
                    None => return Err("unterminated string".into()),
                    Some('"') => break,
                    Some('\\') => {
                        match chars.get(i + 1) {
                            Some(e @ ('"' | '\\')) => s.push(*e),
                            _ => return Err("only \\\" and \\\\ escapes are allowed in a string".into()),
                        }
                        i += 2;
                    }
                    Some(ch) => {
                        s.push(*ch);
                        i += 1;
                    }
                }
            }
            i += 1;
            out.push(Tok::Str(s));
            continue;
        }
        if c == '-' || c.is_ascii_digit() {
            let start = i;
            i += 1;
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
            let digits: String = chars[start..i].iter().collect();
            let value = digits.parse::<i64>().map_err(|_| format!("`{digits}` is not an integer"))?;
            out.push(Tok::Int(value));
            continue;
        }
        if c.is_ascii_alphabetic() {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            out.push(Tok::Word(chars[start..i].iter().collect()));
            continue;
        }
        return Err(format!("unexpected `{c}`"));
    }
    Ok(out)
}

struct Parser {
    toks: Vec<Tok>,
    at: usize,
}

fn show(tok: Option<&Tok>) -> String {
    match tok {
        None => "the end of the law".into(),
        Some(Tok::Word(w)) => format!("`{w}`"),
        Some(Tok::Int(n)) => format!("`{n}`"),
        Some(Tok::Str(s)) => format!("{s:?}"),
        Some(Tok::Punct(p)) => format!("`{p}`"),
    }
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.at)
    }
    fn next(&mut self) -> Option<Tok> {
        let tok = self.toks.get(self.at).cloned();
        self.at += 1;
        tok
    }
    fn is(&self, p: &str) -> bool {
        matches!(self.peek(), Some(Tok::Punct(q)) if *q == p)
    }
    fn is_word(&self, w: &str) -> bool {
        matches!(self.peek(), Some(Tok::Word(v)) if v == w)
    }
    fn expect(&mut self, p: &str) -> Result<(), String> {
        if self.is(p) {
            self.at += 1;
            Ok(())
        } else {
            Err(format!("expected `{p}`, found {}", show(self.peek())))
        }
    }
    fn nat(&mut self, what: &str) -> Result<i64, String> {
        match self.next() {
            Some(Tok::Int(n)) if n >= 0 => Ok(n),
            other => Err(format!("expected {what} (a number), found {}", show(other.as_ref()))),
        }
    }

    fn law(&mut self) -> Result<Value, String> {
        let mut clauses = vec![self.clause()?];
        while self.is(";") {
            self.at += 1;
            if self.peek().is_none() {
                break;
            }
            clauses.push(self.clause()?);
        }
        if self.peek().is_some() {
            return Err(format!("expected `;` or the end of the law, found {}", show(self.peek())));
        }
        Ok(if clauses.len() == 1 {
            clauses.pop().expect("one clause")
        } else {
            json!({"type":"all","predicates":clauses})
        })
    }

    fn clause(&mut self) -> Result<Value, String> {
        let word = match self.peek() {
            Some(Tok::Word(w)) => w.clone(),
            other => return Err(format!("expected a clause, found {}", show(other))),
        };
        match word.as_str() {
            "sealed" => {
                self.at += 1;
                Ok(json!({"type":"any","predicates":[]}))
            }
            "open" => {
                self.at += 1;
                Ok(json!({"type":"all","predicates":[]}))
            }
            "any" | "all" => {
                self.at += 1;
                self.expect("[")?;
                let mut children = Vec::new();
                if !self.is("]") {
                    children.push(self.clause()?);
                    while self.is(",") {
                        self.at += 1;
                        children.push(self.clause()?);
                    }
                }
                self.expect("]")?;
                Ok(json!({"type":word,"predicates":children}))
            }
            "not" => {
                self.at += 1;
                self.expect("(")?;
                let inner = self.clause()?;
                self.expect(")")?;
                Ok(json!({"type":"not","predicate":inner}))
            }
            "witnessed" => Err(
                "witnessed is not a law clause: Mini admits by re-execution and has no proof system, so the clause could never hold"
                    .into(),
            ),
            _ => self.atom(),
        }
    }

    /// The slot a clause reads, and whether it is a field's `after` view.
    fn slot(&mut self) -> Result<(String, bool), String> {
        match self.next() {
            Some(Tok::Word(w)) => match w.as_str() {
                "field" => {
                    let n = self.nat("a field number")?;
                    let view = match self.peek() {
                        Some(Tok::Word(v)) if v == "before" || v == "after" || v == "delta" => {
                            let v = v.clone();
                            self.at += 1;
                            v
                        }
                        _ => "after".into(),
                    };
                    let after = view == "after";
                    Ok((format!("resource/field/{n}/{view}"), after))
                }
                "pair" => {
                    let a = self.nat("the first field of the pair")?;
                    self.expect(",")?;
                    let b = self.nat("the second field of the pair")?;
                    if !self.is_word("delta") {
                        return Err(format!("a pair has only its `delta` view, found {}", show(self.peek())));
                    }
                    self.at += 1;
                    Ok((format!("resource/pair/{a}/{b}/delta"), false))
                }
                "subject" | "verb" | "cost" => Ok((format!("request/{w}"), false)),
                "slot" => match self.next() {
                    Some(Tok::Str(s)) => Ok((s, false)),
                    other => Err(format!("slot takes a quoted slot name, found {}", show(other.as_ref()))),
                },
                _ => Err(format!(
                    "unknown word `{w}`: a clause starts with field, pair, subject, verb, cost, slot, any, all, not, sealed or open"
                )),
            },
            other => Err(format!("expected a clause, found {}", show(other.as_ref()))),
        }
    }

    fn value(&mut self, slot: &str) -> Result<String, String> {
        match self.next() {
            Some(Tok::Int(n)) => Ok(n.to_string()),
            Some(Tok::Word(w)) if slot == "request/verb" => VERBS
                .iter()
                .find(|(name, _)| *name == w)
                .map(|(_, tag)| tag.to_string())
                .ok_or_else(|| format!("unknown verb `{w}` (read, write, delegate, install, revoke)")),
            other => Err(format!("expected a number, found {}", show(other.as_ref()))),
        }
    }

    fn atom(&mut self) -> Result<Value, String> {
        let (slot, after) = self.slot()?;
        let op = match self.next() {
            Some(Tok::Word(w)) if w == "monotone" || w == "writeOnce" || w == "in" => w,
            Some(Tok::Punct(p)) if p == "==" || p == "<=" => p.to_string(),
            other => {
                return Err(format!(
                    "after a slot expected ==, <=, in, monotone or writeOnce, found {}",
                    show(other.as_ref())
                ))
            }
        };
        match op.as_str() {
            "monotone" | "writeOnce" => {
                if !after {
                    return Err(format!(
                        "{op} compares a field's old and new `after` views; on {slot} both views are the same, so it could never refuse"
                    ));
                }
                Ok(json!({"type":op,"slot":slot}))
            }
            "==" => Ok(json!({"type":"eq","slot":slot,"value":self.value(&slot)?})),
            "<=" => Ok(json!({"type":"le","slot":slot,"value":self.value(&slot)?})),
            _ => {
                self.expect("{")?;
                let mut values = vec![self.value(&slot)?];
                while self.is(",") {
                    self.at += 1;
                    values.push(self.value(&slot)?);
                }
                self.expect("}")?;
                Ok(json!({"type":"memberOf","slot":slot,"values":values}))
            }
        }
    }
}

/// Parse law text to the Host's `Pred` JSON.
pub(crate) fn parse(text: &str) -> Result<Value, String> {
    let toks = tokens(text)?;
    if toks.is_empty() {
        return Err("empty law".into());
    }
    Parser { toks, at: 0 }.law()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eq(slot: &str, v: &str) -> Value {
        json!({"type":"eq","slot":slot,"value":v})
    }
    fn not(p: Value) -> Value {
        json!({"type":"not","predicate":p})
    }
    fn any(ps: Vec<Value>) -> Value {
        json!({"type":"any","predicates":ps})
    }
    fn all(ps: Vec<Value>) -> Value {
        json!({"type":"all","predicates":ps})
    }

    #[test]
    fn every_atom_production() {
        let f = "resource/field/2/after";
        assert_eq!(parse("field 2 monotone").unwrap(), json!({"type":"monotone","slot":f}));
        assert_eq!(parse("field 2 after writeOnce").unwrap(), json!({"type":"writeOnce","slot":f}));
        assert_eq!(parse("field 2 == 5").unwrap(), eq(f, "5"));
        assert_eq!(parse("field 2 <= -3").unwrap(), json!({"type":"le","slot":f,"value":"-3"}));
        assert_eq!(
            parse("field 2 in {0,1,2}").unwrap(),
            json!({"type":"memberOf","slot":f,"values":["0","1","2"]})
        );
        assert_eq!(parse("field 0 before == 1").unwrap(), eq("resource/field/0/before", "1"));
        assert_eq!(
            parse("field 3 delta <= 0").unwrap(),
            json!({"type":"le","slot":"resource/field/3/delta","value":"0"})
        );
        assert_eq!(
            parse("pair 2,3 delta <= 0").unwrap(),
            json!({"type":"le","slot":"resource/pair/2/3/delta","value":"0"})
        );
        assert_eq!(parse("subject == 7").unwrap(), eq("request/subject", "7"));
        assert_eq!(parse("cost <= 1000").unwrap(), json!({"type":"le","slot":"request/cost","value":"1000"}));
        assert_eq!(parse(r#"slot "account/balance/3" <= 9"#).unwrap(), json!({"type":"le","slot":"account/balance/3","value":"9"}));
        assert!(parse(r#"witnessed "vk-1""#).unwrap_err().contains("no proof system"));
    }

    #[test]
    fn verbs_by_name_are_the_request_verb_tags() {
        assert_eq!(parse("verb == write").unwrap(), eq("request/verb", "2"));
        assert_eq!(parse("verb == 2").unwrap(), eq("request/verb", "2"));
        assert_eq!(
            parse("verb in {read,delegate,install,revoke}").unwrap(),
            json!({"type":"memberOf","slot":"request/verb","values":["1","3","4","5"]})
        );
        assert!(parse("verb == mutate").unwrap_err().contains("unknown verb"));
        assert!(parse("field 2 == write").is_err());
    }

    #[test]
    fn nesting_sealed_open_and_clause_lists() {
        assert_eq!(parse("sealed").unwrap(), any(vec![]));
        assert_eq!(parse("open").unwrap(), all(vec![]));
        assert_eq!(parse("any []").unwrap(), any(vec![]));
        assert_eq!(
            parse("any [ field 2 monotone, not (verb == write) ]").unwrap(),
            any(vec![json!({"type":"monotone","slot":"resource/field/2/after"}), not(eq("request/verb", "2"))])
        );
        assert_eq!(
            parse("subject == 7; field 1 == 0;").unwrap(),
            all(vec![eq("request/subject", "7"), eq("resource/field/1/after", "0")])
        );
        assert_eq!(parse("all [ open, not (sealed) ]").unwrap(), all(vec![all(vec![]), not(any(vec![]))]));
    }

    #[test]
    fn refusals_name_the_problem() {
        assert!(parse("").is_err());
        assert!(parse("field state monotone").unwrap_err().contains("field number"));
        assert!(parse("field 2 before monotone").unwrap_err().contains("could never refuse"));
        assert!(parse("field 2 delta writeOnce").unwrap_err().contains("could never refuse"));
        assert!(parse("pair 2,3 == 0").unwrap_err().contains("delta"));
        assert!(parse("not field 2 == 1").unwrap_err().contains("expected `(`"));
        assert!(parse("any [ field 2 == 1").unwrap_err().contains("expected `]`"));
        assert!(parse("field 2 == 1 field 3 == 1").unwrap_err().contains("expected `;`"));
        assert!(parse("owner == 3").unwrap_err().contains("unknown word"));
        assert!(parse("subject == {GM}").is_err());
    }

    /// The Host renders a refused clause in this grammar
    /// (`Compiler/RefusalReason.lean` `LawLeaf.renderClause`); its rendered
    /// samples parse back to the clauses it rendered.
    #[test]
    fn host_renderings_parse_back() {
        assert_eq!(parse("field 2 monotone").unwrap(), json!({"type":"monotone","slot":"resource/field/2/after"}));
        assert_eq!(
            parse("any [ field 0 delta == 0, all [ field 0 before == 0, field 0 == 1 ] ]").unwrap(),
            any(vec![
                eq("resource/field/0/delta", "0"),
                all(vec![eq("resource/field/0/before", "0"), eq("resource/field/0/after", "1")]),
            ])
        );
        assert_eq!(
            parse("any [ verb == read, verb == write, all [ verb in {delegate,install,revoke}, subject == 7 ] ]").unwrap(),
            any(vec![
                eq("request/verb", "1"),
                eq("request/verb", "2"),
                all(vec![
                    json!({"type":"memberOf","slot":"request/verb","values":["3","4","5"]}),
                    eq("request/subject", "7"),
                ]),
            ])
        );
    }

    /// `deploy/shell/templates/story/tale/law.state` (branch p-templates) with
    /// `{GM}` = 11: the grammar text and the JSON rendered from it by the
    /// templates lane agree.
    #[test]
    fn templates_law_state_agrees() {
        let text = "any [ subject == 11, not (verb == 2) ];\n\
                    any [ field 0 in {0,1,2,3,4}, not (verb == 2) ];\n\
                    any [ field 0 monotone, not (verb == 2) ];\n\
                    any [ field 0 delta == 0,\n      all [ field 0 before == 0, field 0 after == 1 ],\n      not (verb == 2) ]\n";
        let guard = not(eq("request/verb", "2"));
        assert_eq!(
            parse(text).unwrap(),
            all(vec![
                any(vec![eq("request/subject", "11"), guard.clone()]),
                any(vec![
                    json!({"type":"memberOf","slot":"resource/field/0/after","values":["0","1","2","3","4"]}),
                    guard.clone(),
                ]),
                any(vec![json!({"type":"monotone","slot":"resource/field/0/after"}), guard.clone()]),
                any(vec![
                    eq("resource/field/0/delta", "0"),
                    all(vec![eq("resource/field/0/before", "0"), eq("resource/field/0/after", "1")]),
                    guard,
                ]),
            ])
        );
    }
}
