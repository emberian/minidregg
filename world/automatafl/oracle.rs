// Wire adapter only. All game decisions run automatafl-logic's actual code.
use automatafl_logic::*;
use serde_json::{Value, json};
use std::io::{self, BufRead};

fn num(v: &Value, key: &str) -> usize { v[key].as_u64().unwrap() as usize }
fn particle(n: u64) -> Particle {
    match n { 0 => Particle::Vacuum, 1 => Particle::Attractor,
        2 => Particle::Repulsor, 3 => Particle::Automaton, _ => panic!("particle") }
}
fn code(p: Particle) -> u8 {
    match p { Particle::Vacuum => 0, Particle::Attractor => 1,
        Particle::Repulsor => 2, Particle::Automaton => 3 }
}
fn run(v: Value) -> Value {
    let w = num(&v, "w"); let h = num(&v, "h"); let a = num(&v, "a");
    let coord = |i: usize| Coord { x: (i % w) as u8, y: (i / w) as u8 };
    let cells = v["cells"].as_array().unwrap().iter().map(|n| Cell {
        what: particle(n.as_u64().unwrap()), conflict: false, passable: false
    }).collect();
    let board = Board { particles: ndarray::Array2::from_shape_vec((h,w),cells).unwrap(),
        size: Coord { x: w as u8, y: h as u8 }, automaton_location: coord(a),
        conflict_list: Default::default(), passable_list: Default::default() };
    // Exactly TWO players; the extra modes of the n-player implementation are never used.
    let mut g = Game::new_default_modes(board, 2, true);
    for mark in v["marks"].as_array().unwrap() { g.board.mark_conflict(coord(mark.as_u64().unwrap() as usize)); }
    if v["kind"] == "automaton" {
        return json!({"a":g.automaton_move().to_key(w as u8)});
    }
    let mut proposals = vec![];
    for (who, m) in v["moves"].as_array().unwrap().iter().enumerate() {
        let feedback = g.propose_move(Move { who: Pid(who as u8),
            from: coord(m[0].as_u64().unwrap() as usize), to: coord(m[1].as_u64().unwrap() as usize) });
        proposals.push(format!("{feedback:?}"));
        if matches!(feedback, ProposeFeedback::Rejected(_)) {
            return json!({"rejected":true,"proposals":proposals});
        }
    }
    let feedback = g.try_complete_round();
    let status = if matches!(feedback, CompleteRoundFeedback::Conflict(_)) { 1 } else { 0 };
    let cells: Vec<_> = g.board.particles.iter().map(|c| code(c.what)).collect();
    let marks: Vec<_> = g.board.particles.iter().enumerate().filter(|(_,c)|c.conflict).map(|(i,_)|i).collect();
    json!({"cells":cells,"a":g.board.automaton_location.to_key(w as u8),"marks":marks,
        "status":status,"winner":g.winner.map(|p|p.0+1).unwrap_or(0),"feedback":format!("{feedback:?}")})
}
fn main() {
    for line in io::stdin().lock().lines() {
        let v: Value = serde_json::from_str(&line.unwrap()).unwrap();
        let id = v["id"].clone();
        let result = std::panic::catch_unwind(|| run(v));
        let out = match result { Ok(out) => out, Err(_) => json!({"panic":true}) };
        println!("{}",json!({"id":id,"result":out}));
    }
}
