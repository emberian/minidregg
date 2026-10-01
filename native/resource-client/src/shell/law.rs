//! The shell's one-line law grammar. It renders to the Host's existing `Pred`
//! JSON (`Host/Json.lean` `predicate`) and adds no semantics: every production
//! is one `Pred` constructor over one projected slot.
//!
//! ```text
//! law    := clause (';' clause)* [';']        one clause is itself; more are `all`
//! clause := 'sealed' | 'open'                 any [] | all []
//!         | ('any' | 'all') '[' [clause (',' clause)*] ']'
//!         | 'not' '(' clause ')'
//!         | 'ran' N                           ran: the command's run claim for program N re-executed
//!         | field ('monotone' | 'writeOnce')
//!         | slot ('==' value | '<=' value | 'in' '{' value (',' value)* '}')
//!         | slot '==' slot                    eqSlots: both present and equal
//!         | slot '<=' slot ['+' integer]      leSlots / leSlotsOff: new[a] <= new[b] (+ k)
//!         | slot 'opens' '(' slot (',' slot)* ')' 'with' slot
//!                                             hashEq: the first slot holds the cSHAKE256
//!                                             commitment to the tuple, under the blinder slot
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
//! `ran N` (K-RAN, policy tag 14) holds when the controller projects
//! `run/program/N`: the command carried a run claim for program N that the
//! kernel re-executed, and the command's writes are the program's product.
//! The Host renders it `ran N`.
//!
//! There is no `witnessed` clause: Mini admits by re-execution, and with no
//! proof system in admission (decision 10-01) the `witnessed` atom compiles to
//! false, so a law that named it would refuse every write. The grammar refuses
//! the word instead of offering a clause that can never hold.
//!
//! The slot-to-slot atoms (`eqSlots`, `leSlots`, `leSlotsOff`) are spelled the way
//! the Host renders them (`Compiler/RefusalReason.lean` `renderClause`):
//! `field 7 before <= slot "clock/now"`, `field 14 <= slot "clock/now" + -1`.
//! A slot-pair atom is false when either slot is absent, so `field 15 == field 15`
//! is "field 15 is present" (the job law, `deploy/shell/templates/job/law.job.shell`).
//!
//! `field 17 opens (field 18, field 19) with field 20` is commit–reveal of a tuple
//! (`Pred.hashEq`, `Pred/HashEq.lean`): field 17 must hold
//! `cSHAKE256("DREGG.PRED.HASHEQ/v2"; cell ‖ n ‖ names ‖ values ‖ blinder)` of the
//! new values of fields 18 and 19 under the blinder in field 20. Every field of the
//! tuple is opened at once; a reveal missing one is refused. It is spelled the way
//! the Host renders it in a refusal, and `law show` prints an installed law back in
//! this grammar from the Host's own rendering.

use serde_json::{json, Value};

const VERBS: [(&str, i64); 5] = [("read", 1), ("write", 2), ("delegate", 3), ("install", 4), ("revoke", 5)];

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Word(String),
    /// A canonical signed decimal of any width (`-0` and leading zeros refused): the
    /// Host's `int` reader takes any width, and subjects and commitments exceed `i64`.
    Int(String),
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
        if let Some(p) = ["[", "]", "(", ")", "{", "}", ",", ";", "+"].into_iter().find(|p| p.starts_with(c)) {
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
            let magnitude = digits.strip_prefix('-').unwrap_or(&digits);
            if magnitude.is_empty() || (magnitude.len() > 1 && magnitude.starts_with('0')) || digits == "-0" {
                return Err(format!("`{digits}` is not a canonical integer"));
            }
            out.push(Tok::Int(digits));
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
    fn nat(&mut self, what: &str) -> Result<String, String> {
        match self.next() {
            Some(Tok::Int(n)) if !n.starts_with('-') => Ok(n),
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
            "ran" => {
                self.at += 1;
                let program = self.nat("a program id")?;
                Ok(json!({"type":"ran","program":program}))
            }
            "witnessed" => Err(
                "witnessed is not a law clause: Mini admits by re-execution and has no proof system, so the clause could never hold"
                    .into(),
            ),
            _ => self.atom(),
        }
    }

    /// Whether the next token starts a slot (the right side of a slot-to-slot atom).
    fn at_slot(&self) -> bool {
        matches!(self.peek(), Some(Tok::Word(w)) if matches!(w.as_str(), "field" | "pair" | "subject" | "verb" | "cost" | "slot"))
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
            Some(Tok::Int(n)) => Ok(n),
            Some(Tok::Word(w)) if slot == "request/verb" => VERBS
                .iter()
                .find(|(name, _)| *name == w)
                .map(|(_, tag)| tag.to_string())
                .ok_or_else(|| format!("unknown verb `{w}` (read, write, delegate, install, revoke)")),
            other => Err(format!("expected a number, found {}", show(other.as_ref()))),
        }
    }

    /// `C opens (V1, …, Vn) with B`, after the commit slot `C` and the word `opens`.
    fn opens(&mut self, commit: String) -> Result<Value, String> {
        if !self.is("(") {
            return Err(format!(
                "`opens` takes the opened slots in parentheses, `opens (field 3, field 4) with field 5`; found {}",
                show(self.peek())
            ));
        }
        self.at += 1;
        if self.is(")") {
            return Err("`opens ()` opens nothing: name at least one slot".into());
        }
        let mut values = vec![self.slot()?.0];
        while self.is(",") {
            self.at += 1;
            values.push(self.slot()?.0);
        }
        self.expect(")")?;
        if !self.is_word("with") {
            return Err(format!("after the opened slots expected `with` and the blinder slot, found {}", show(self.peek())));
        }
        self.at += 1;
        let blinder = self.slot()?.0;
        let mut named = values.clone();
        named.push(blinder.clone());
        named.push(commit.clone());
        let mut sorted = named.clone();
        sorted.sort();
        sorted.dedup();
        if sorted.len() != named.len() {
            return Err("`opens` names one slot twice: the commit, the blinder and each opened slot must differ".into());
        }
        Ok(json!({"type":"hashEq","values":values,"blinder":blinder,"commit":commit}))
    }

    fn atom(&mut self) -> Result<Value, String> {
        let (slot, after) = self.slot()?;
        let op = match self.next() {
            Some(Tok::Word(w)) if w == "opens" => return self.opens(slot),
            Some(Tok::Word(w)) if w == "monotone" || w == "writeOnce" || w == "in" => w,
            Some(Tok::Punct(p)) if p == "==" || p == "<=" => p.to_string(),
            other => {
                return Err(format!(
                    "after a slot expected ==, <=, in, monotone, writeOnce or opens, found {}",
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
            "==" | "<=" if self.at_slot() => {
                let (right, _) = self.slot()?;
                if op == "==" {
                    return Ok(json!({"type":"eqSlots","left":slot,"right":right}));
                }
                if !self.is("+") {
                    return Ok(json!({"type":"leSlots","left":slot,"right":right}));
                }
                self.at += 1;
                match self.next() {
                    Some(Tok::Int(k)) => Ok(json!({"type":"leSlotsOff","left":slot,"right":right,"offset":k})),
                    other => Err(format!("after `+` expected an integer offset, found {}", show(other.as_ref()))),
                }
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
        // subjects and commitments are wider than i64
        assert_eq!(parse("subject == 18424463879702066335").unwrap(), eq("request/subject", "18424463879702066335"));
        assert_eq!(
            parse("field 2 == 115792089237316195423570985008687907853269984665640564039457584007913129639935").unwrap(),
            eq(f, "115792089237316195423570985008687907853269984665640564039457584007913129639935")
        );
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
        assert!(parse("field 2 == 007").unwrap_err().contains("canonical"));
        assert!(parse("field 2 == -0").unwrap_err().contains("canonical"));
        assert!(parse("field -2 == 1").unwrap_err().contains("field number"));
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

    /// The slot-to-slot atoms, in the Host's rendering (`renderClause`).
    #[test]
    fn slot_pair_atoms() {
        assert_eq!(
            parse("field 15 == field 12").unwrap(),
            json!({"type":"eqSlots","left":"resource/field/15/after","right":"resource/field/12/after"})
        );
        assert_eq!(
            parse(r#"slot "clock/now" <= field 6"#).unwrap(),
            json!({"type":"leSlots","left":"clock/now","right":"resource/field/6/after"})
        );
        assert_eq!(
            parse(r#"field 14 <= slot "clock/now" + -1"#).unwrap(),
            json!({"type":"leSlotsOff","left":"resource/field/14/after","right":"clock/now","offset":"-1"})
        );
        assert_eq!(
            parse(r#"field 14 <= slot "clock/now" + 600"#).unwrap(),
            json!({"type":"leSlotsOff","left":"resource/field/14/after","right":"clock/now","offset":"600"})
        );
        assert_eq!(
            parse("subject == field 9").unwrap(),
            json!({"type":"eqSlots","left":"request/subject","right":"resource/field/9/after"})
        );
        assert_eq!(
            parse("field 0 before == field 0 before").unwrap(),
            json!({"type":"eqSlots","left":"resource/field/0/before","right":"resource/field/0/before"})
        );
        assert!(parse(r#"field 14 <= slot "clock/now" + x"#).unwrap_err().contains("integer offset"));
        assert!(parse("field 14 == field 2 + 1").unwrap_err().contains("expected `;`"));
    }

    /// `ran N` is K-RAN's atom at any program id width (a programId is a 256-bit
    /// digest value), and a field value is not an `i64` either.
    #[test]
    fn ran_and_wide_values() {
        let id = "93720198387429108465912876439187263948172639481726394817263948172639481726394";
        assert_eq!(parse(&format!("ran {id}")).unwrap(), json!({"type":"ran","program":id}));
        assert_eq!(
            parse(&format!("field 1 == {id}")).unwrap(),
            json!({"type":"eq","slot":"resource/field/1/after","value":id})
        );
        assert!(parse("ran -3").unwrap_err().contains("a program id"));
    }

    /// Commit–reveal of a tuple: the Host's rendering of `Pred.hashEq`
    /// (`Compiler/RefusalReason.lean` `renderClause`) parses to its JSON.
    #[test]
    fn opens_is_the_tuple_hash_atom() {
        let f = |n: u32| format!("resource/field/{n}/after");
        assert_eq!(
            parse("field 17 opens (field 18, field 19) with field 20").unwrap(),
            json!({"type":"hashEq","values":[f(18),f(19)],"blinder":f(20),"commit":f(17)})
        );
        assert_eq!(
            parse("field 2 opens (field 3) with field 4").unwrap(),
            json!({"type":"hashEq","values":[f(3)],"blinder":f(4),"commit":f(2)})
        );
        assert_eq!(
            parse(r#"slot "x/commit" opens (slot "x/a", field 5, slot "x/b") with slot "x/r""#).unwrap(),
            json!({"type":"hashEq","values":["x/a",f(5),"x/b"],"blinder":"x/r","commit":"x/commit"})
        );
        assert_eq!(
            parse("any [ field 17 delta == 0, all [ verb == write, field 17 opens (field 18, field 19) with field 20 ] ]").unwrap(),
            any(vec![
                eq("resource/field/17/delta", "0"),
                all(vec![
                    eq("request/verb", "2"),
                    json!({"type":"hashEq","values":[f(18),f(19)],"blinder":f(20),"commit":f(17)}),
                ]),
            ])
        );
        assert!(parse("field 17 opens field 18 with field 20").unwrap_err().contains("parentheses"));
        assert!(parse("field 17 opens () with field 20").unwrap_err().contains("opens nothing"));
        assert!(parse("field 17 opens (field 18, field 19) field 20").unwrap_err().contains("`with`"));
        assert!(parse("field 17 opens (field 18) with").unwrap_err().contains("expected a clause"));
        assert!(parse("field 17 opens (field 18, field 18) with field 20").unwrap_err().contains("twice"));
        assert!(parse("field 17 opens (field 18) with field 17").unwrap_err().contains("twice"));
        assert!(parse("field 17 opens (field 18) with field 20 + 1").unwrap_err().contains("expected `;`"));
    }

    /// The job law (COMPUTE §2.3, `Kernel/Job.lean`): the shell grammar text
    /// `law.job.shell` (the Host's rendering of every clause, written by
    /// `scripts/gen-joblaw.py`) parses to exactly `law.job.json`, both with the
    /// same placeholder binding.
    #[test]
    fn job_law_grammar_is_the_template_json() {
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../deploy/shell/templates/job/");
        let bind = |s: String| {
            s.replace("{CALLER}", "7")
                .replace("{PROGRAM}", "42")
                .replace("{NEG_WINDOW}", "-600")
                .replace("{WINDOW}", "600")
        };
        let file = std::fs::read_to_string(format!("{dir}law.job.shell")).expect("law.job.shell");
        let text = bind(file.lines().filter(|l| !l.starts_with("--")).collect::<Vec<_>>().join("\n"));
        let json: Value =
            serde_json::from_str(&bind(std::fs::read_to_string(format!("{dir}law.job.json")).expect("law.job.json")))
                .expect("law.job.json parses");
        let parsed = parse(&text).expect("the job law parses");
        assert_eq!(parsed["predicates"].as_array().map(Vec::len), Some(45));
        assert_eq!(parsed, json);
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
