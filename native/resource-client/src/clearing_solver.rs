//! Deterministic client-side `Cert-F` primal-dual uniform-price market clearing solver
//! mirroring `Kernel/CertifiedClearing.lean` and `Theory/CertF.lean`.
//!
//! Given a `Market { currency, goods, epsilon }` and open `Bid`/`Ask` orders, this module:
//! 1. Deterministically selects an integer clearing `price` maximizing cleared goods volume,
//! 2. Routes matched goods and currency transfers (`moves: Vec<Transfer>`) at `price`,
//! 3. Synthesizes dual potentials `(bid_potential, ask_potential)` and per-seat `slacks`, and
//! 4. Self-verifies every inequality checked by `Kernel.CertifiedClearing.judge` (`verify_cert_f`)
//!    before returning the certificate.

use crate::Result;
use serde_json::{json, Value};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Market {
    pub currency: u64,
    pub goods: u64,
    pub epsilon: u128,
}

impl Default for Market {
    fn default() -> Self {
        Self {
            currency: 1,
            goods: 2,
            epsilon: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Side {
    Bid,
    Ask,
}

impl Side {
    /// Incidence sign in row 0 of `CertifiedClearing.incidence`:
    /// `Bid => -1`, `Ask => 1`.
    pub(crate) fn out(self) -> i128 {
        match self {
            Self::Bid => -1,
            Self::Ask => 1,
        }
    }

    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Bid => "bid",
            Self::Ask => "ask",
        }
    }

    pub(crate) fn parse(raw: &str) -> Result<Self> {
        match raw.trim().to_ascii_lowercase().as_str() {
            "bid" | "buy" | "b" => Ok(Self::Bid),
            "ask" | "sell" | "offer" | "a" => Ok(Self::Ask),
            other => Err(format!("unknown order role `{other}` (expected `bid` or `ask`)").into()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Order {
    pub seat: u64,
    pub role: Side,
    pub limit_price: u128,
    pub max_goods: u128,
    /// Total currency budget (for `Bid`) or reserve (for `Ask`), matching `Order.total` in
    /// `Kernel/CertifiedClearing.lean`. For standard limit orders, `total == limit_price * max_goods`.
    pub total: u128,
}

impl Order {
    pub(crate) fn bid(seat: u64, limit_price: u128, max_goods: u128) -> Self {
        Self {
            seat,
            role: Side::Bid,
            limit_price,
            max_goods,
            total: limit_price.saturating_mul(max_goods),
        }
    }

    pub(crate) fn ask(seat: u64, limit_price: u128, max_goods: u128) -> Self {
        Self {
            seat,
            role: Side::Ask,
            limit_price,
            max_goods,
            total: limit_price.saturating_mul(max_goods),
        }
    }

    pub(crate) fn from_give_want(
        market: &Market,
        seat: u64,
        give_asset: u64,
        give_amount: u128,
        want_asset: u64,
        want_amount: u128,
    ) -> Result<Self> {
        if give_asset == market.currency && want_asset == market.goods {
            if want_amount == 0 {
                return Err(format!("seat {seat}: bid want_amount (goods) must be > 0").into());
            }
            Ok(Self {
                seat,
                role: Side::Bid,
                limit_price: give_amount / want_amount,
                max_goods: want_amount,
                total: give_amount,
            })
        } else if give_asset == market.goods && want_asset == market.currency {
            if give_amount == 0 {
                return Err(format!("seat {seat}: ask give_amount (goods) must be > 0").into());
            }
            Ok(Self {
                seat,
                role: Side::Ask,
                limit_price: want_amount.div_ceil(give_amount),
                max_goods: give_amount,
                total: want_amount,
            })
        } else {
            Err(format!(
                "seat {seat}: assets ({give_asset} -> {want_asset}) do not match market (currency={}, goods={})",
                market.currency, market.goods
            )
            .into())
        }
    }

    /// `Order.crosses` in `Kernel/CertifiedClearing.lean` (lines 163–166):
    /// - `Bid`: `price * qty <= total`
    /// - `Ask`: `total <= price * qty`
    pub(crate) fn crosses(&self, price: u128) -> bool {
        let notional = price.saturating_mul(self.max_goods);
        match self.role {
            Side::Bid => notional <= self.total,
            Side::Ask => self.total <= notional,
        }
    }

    /// Capacity `c(e)` in `Kernel/CertifiedClearing.lean` (`lpOf`).
    pub(crate) fn capacity_at(&self, price: u128) -> i128 {
        if self.crosses(price) {
            self.max_goods as i128
        } else {
            0
        }
    }

    /// Goods filled for this order under `moves` (`Order.fill` in `Kernel/CertifiedClearing.lean`).
    pub(crate) fn fill(&self, moves: &[Transfer], market: &Market) -> i128 {
        let flow = net_flow(moves, self.seat, market.goods);
        match self.role {
            Side::Bid => flow,
            Side::Ask => -flow,
        }
    }

    /// Currency paid/received for this order under `moves` (`Order.paid` in `Kernel/CertifiedClearing.lean`).
    pub(crate) fn paid(&self, moves: &[Transfer], market: &Market) -> i128 {
        let flow = net_flow(moves, self.seat, market.currency);
        match self.role {
            Side::Bid => -flow,
            Side::Ask => flow,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Transfer {
    pub from: u64,
    pub to: u64,
    pub asset: u64,
    pub amount: u128,
}

impl Transfer {
    pub(crate) fn to_json(&self) -> Value {
        json!({
            "from": self.from,
            "to": self.to,
            "source": self.from,
            "destination": self.to,
            "asset": self.asset,
            "amount": self.amount,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Certificate {
    pub price: u128,
    pub bid_potential: i128,
    pub ask_potential: i128,
    pub slacks: Vec<i128>,
}

impl Certificate {
    pub(crate) fn to_json(&self) -> Value {
        json!({
            "price": self.price,
            "bidPotential": self.bid_potential,
            "askPotential": self.ask_potential,
            "slacks": self.slacks,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OrderFill {
    pub seat: u64,
    pub role: Side,
    pub limit_price: u128,
    pub max_goods: u128,
    pub crosses: bool,
    pub capacity: u128,
    pub fill: u128,
    pub paid: u128,
    pub slack: i128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClearingSolution {
    pub market: Market,
    pub orders: Vec<Order>,
    pub moves: Vec<Transfer>,
    pub cert: Certificate,
    pub fills: Vec<OrderFill>,
    pub volume: u128,
    pub primal_objective: i128,
    pub dual_objective: i128,
    pub duality_gap: i128,
}

impl ClearingSolution {
    pub(crate) fn to_json(&self) -> Value {
        let moves_json: Vec<Value> = self.moves.iter().map(Transfer::to_json).collect();
        let fills_json: Vec<Value> = self
            .fills
            .iter()
            .map(|f| {
                json!({
                    "seat": f.seat,
                    "units": f.fill,
                    "role": f.role.as_str(),
                    "limitPrice": f.limit_price,
                    "maxGoods": f.max_goods,
                    "crosses": f.crosses,
                    "capacity": f.capacity,
                    "fill": f.fill,
                    "paid": f.paid,
                    "slack": f.slack,
                })
            })
            .collect();
        let drex_fills: Vec<Value> = self
            .fills
            .iter()
            .filter(|f| f.fill > 0)
            .map(|f| {
                json!({
                    "seat": f.seat,
                    "units": f.fill,
                })
            })
            .collect();
        let cert_json = self.cert.to_json();
        let action = json!({
            "action": "clear",
            "price": self.cert.price,
            "bidPotential": self.cert.bid_potential,
            "askPotential": self.cert.ask_potential,
            "slacks": self.cert.slacks,
            "moves": moves_json,
            "fills": drex_fills,
            "certificate": cert_json,
            "market": {
                "currency": self.market.currency,
                "goods": self.market.goods,
                "epsilon": self.market.epsilon,
            },
        });
        json!({
            "verified": true,
            "market": {
                "currency": self.market.currency,
                "goods": self.market.goods,
                "epsilon": self.market.epsilon,
            },
            "price": self.cert.price,
            "volume": self.volume,
            "primalObjective": self.primal_objective,
            "dualObjective": self.dual_objective,
            "dualityGap": self.duality_gap,
            "bidPotential": self.cert.bid_potential,
            "askPotential": self.cert.ask_potential,
            "slacks": self.cert.slacks,
            "moves": moves_json,
            "fills": fills_json,
            "certificate": self.cert.to_json(),
            "seatInvokeAction": action,
        })
    }
}

/// Net flow of `asset` into `seat` across `moves` (`netFlow` in `Kernel/CertifiedClearing.lean`).
pub(crate) fn net_flow(moves: &[Transfer], seat: u64, asset: u64) -> i128 {
    let mut total = 0i128;
    for t in moves {
        if t.asset == asset {
            if t.to == seat {
                total = total.saturating_add(t.amount as i128);
            }
            if t.from == seat {
                total = total.saturating_sub(t.amount as i128);
            }
        }
    }
    total
}

/// Exact Rust mirror of `Kernel.CertifiedClearing.judge` (`Kernel/CertifiedClearing.lean` lines 198–218)
/// and `Theory.CertF.checkCertified` (`Theory/CertF.lean` lines 60–97).
///
/// Verifies:
/// 1. Market non-degeneracy (`currency != goods`), distinct seat accounts, and positive order quantities (`max_goods > 0`),
/// 2. `slackCount`: `cert.slacks.len() == orders.len()`,
/// 3. `foreignAsset`: every transfer moves `market.currency` or `market.goods` with `amount > 0` and `from != to`,
/// 4. `notAnOrder` / `movesConsistent`: every transfer endpoint belongs to an order seat in `orders` with `goods` moving `Ask -> Bid` and `currency` moving `Bid -> Ask`,
/// 5. `notUniform`: for every order, `paid == cert.price * fill`,
/// 6. `PrimalFeasible`: flow conservation `A * f == 0` and box constraints `0 <= fill <= capacity(price)`
///    (which together with `paid == price * fill` implies price improvement / budget / reserve),
/// 7. `DualFeasible`: `slack >= 0` and `1 <= (π ᵥ* A)_e + slack_e` for every order `e`,
/// 8. Complementary slackness / duality gap: `c ⬝ s - w ⬝ f <= market.epsilon`.
pub(crate) fn verify_cert_f(
    market: &Market,
    orders: &[Order],
    moves: &[Transfer],
    cert: &Certificate,
) -> Result<()> {
    if market.currency == market.goods {
        return Err("degenerateMarket: market currency and goods assets must be distinct".into());
    }
    let mut seen_seats = std::collections::BTreeSet::new();
    for (idx, o) in orders.iter().enumerate() {
        if o.max_goods == 0 {
            return Err(format!("invalidOrder[{idx}]: seat {} max_goods must be > 0", o.seat).into());
        }
        if !seen_seats.insert(o.seat) {
            return Err(format!(
                "duplicateSeat: order[{idx}] seat {} appears multiple times in orders",
                o.seat
            )
            .into());
        }
    }
    if cert.slacks.len() != orders.len() {
        return Err(format!(
            "slackCount: expected {} slacks, got {}",
            orders.len(),
            cert.slacks.len()
        )
        .into());
    }
    for (idx, t) in moves.iter().enumerate() {
        if t.amount == 0 {
            return Err(format!("zeroTransfer: transfer[{idx}] has amount 0").into());
        }
        if t.from == t.to {
            return Err(format!(
                "selfTransfer: transfer[{idx}] source and destination seat {} are identical",
                t.from
            )
            .into());
        }
        if t.asset != market.currency && t.asset != market.goods {
            return Err(format!(
                "foreignAsset: transfer[{idx}] asset {} is neither currency ({}) nor goods ({})",
                t.asset, market.currency, market.goods
            )
            .into());
        }
        let Some(src) = orders.iter().find(|o| o.seat == t.from) else {
            return Err(format!(
                "notAnOrder: transfer[{idx}] source seat {} is not in orders",
                t.from
            )
            .into());
        };
        let Some(dst) = orders.iter().find(|o| o.seat == t.to) else {
            return Err(format!(
                "notAnOrder: transfer[{idx}] destination seat {} is not in orders",
                t.to
            )
            .into());
        };
        if t.asset == market.goods && (src.role != Side::Ask || dst.role != Side::Bid) {
            return Err(format!(
                "movesConsistent: goods transfer[{idx}] ({} -> {}) must flow from ask to bid",
                t.from, t.to
            )
            .into());
        }
        if t.asset == market.currency && (src.role != Side::Bid || dst.role != Side::Ask) {
            return Err(format!(
                "movesConsistent: currency transfer[{idx}] ({} -> {}) must flow from bid to ask",
                t.from, t.to
            )
            .into());
        }
    }

    let price_i = cert.price as i128;
    let mut row0_flow = 0i128;
    let mut row1_flow = 0i128;
    let mut w_dot_f = 0i128;
    let mut c_dot_s = 0i128;

    for (j, order) in orders.iter().enumerate() {
        let f = order.fill(moves, market);
        let p = order.paid(moves, market);
        if p != price_i.saturating_mul(f) {
            return Err(format!(
                "notUniform: seat {} paid {} != price ({}) * fill ({})",
                order.seat, p, cert.price, f
            )
            .into());
        }

        let cap = order.capacity_at(cert.price);
        if f < 0 || f > cap {
            return Err(format!(
                "primalBox: seat {} fill {} outside [0, {}] at price {}",
                order.seat, f, cap, cert.price
            )
            .into());
        }

        let sign = order.role.out();
        row0_flow = row0_flow.saturating_add(sign.saturating_mul(f));
        row1_flow = row1_flow.saturating_add((-sign).saturating_mul(f));

        let s = cert.slacks[j];
        if s < 0 {
            return Err(format!("dualSlackNeg: order[{j}] (seat {}) slack {s} < 0", order.seat).into());
        }

        let pi_a = cert
            .bid_potential
            .saturating_mul(sign)
            .saturating_add(cert.ask_potential.saturating_mul(-sign));
        if 1 > pi_a.saturating_add(s) {
            return Err(format!(
                "dualInfeasible: order[{j}] (seat {}) requires 1 <= (pi * A) ({pi_a}) + slack ({s})",
                order.seat
            )
            .into());
        }

        w_dot_f = w_dot_f.saturating_add(f);
        c_dot_s = c_dot_s.saturating_add(cap.saturating_mul(s));
    }

    if row0_flow != 0 || row1_flow != 0 {
        return Err(format!(
            "primalConservation: net goods flow imbalance (row0={row0_flow}, row1={row1_flow})"
        )
        .into());
    }

    let gap = c_dot_s.saturating_sub(w_dot_f);
    if gap > (market.epsilon as i128) {
        return Err(format!(
            "dualityGap: c.s ({c_dot_s}) - w.f ({w_dot_f}) = {gap} > epsilon ({})",
            market.epsilon
        )
        .into());
    }

    Ok(())
}

/// Deterministically solve for the uniform clearing price, matched transfers, and `Cert-F`
/// primal-dual witness, then self-verify with `verify_cert_f`.
pub(crate) fn solve_clearing(market: &Market, orders: &[Order]) -> Result<ClearingSolution> {
    if market.currency == market.goods {
        return Err("market currency and goods assets must be distinct".into());
    }
    let mut seen_seats = std::collections::BTreeSet::new();
    for (idx, o) in orders.iter().enumerate() {
        if o.max_goods == 0 {
            return Err(format!("order[{idx}] (seat {}): max_goods must be > 0", o.seat).into());
        }
        if !seen_seats.insert(o.seat) {
            return Err(format!(
                "duplicate seat {} in order book (each order must belong to a distinct seat)",
                o.seat
            )
            .into());
        }
    }

    // Collect deterministic candidate clearing prices from all order thresholds and midpoints.
    let mut candidates = std::collections::BTreeSet::new();
    let mut bid_limits = Vec::new();
    let mut ask_limits = Vec::new();
    for o in orders {
        let floor_p = o.total / o.max_goods;
        let ceil_p = o.total.div_ceil(o.max_goods);
        candidates.insert(o.limit_price);
        candidates.insert(floor_p);
        candidates.insert(ceil_p);
        match o.role {
            Side::Bid => bid_limits.push(floor_p),
            Side::Ask => ask_limits.push(ceil_p),
        }
    }
    for &b in &bid_limits {
        for &a in &ask_limits {
            if a <= b {
                candidates.insert(a + (b - a) / 2);
            }
        }
    }
    if candidates.is_empty() {
        candidates.insert(0);
    }

    // Evaluate each candidate price p:
    // B(p) = total crossing bid quantity, S(p) = total crossing ask quantity, V(p) = min(B(p), S(p)).
    // Maximize V(p); break ties by minimizing |B(p) - S(p)|, then preferring positive price, then smaller price.
    let mut best_price = *candidates.first().unwrap_or(&0);
    let mut best_vol = 0u128;
    let mut best_imbalance = u128::MAX;

    for &p in &candidates {
        let b_cap: u128 = orders
            .iter()
            .filter(|o| o.role == Side::Bid && o.crosses(p))
            .map(|o| o.max_goods)
            .sum();
        let s_cap: u128 = orders
            .iter()
            .filter(|o| o.role == Side::Ask && o.crosses(p))
            .map(|o| o.max_goods)
            .sum();
        let vol = b_cap.min(s_cap);
        let imbalance = b_cap.abs_diff(s_cap);
        let better = if vol != best_vol {
            vol > best_vol
        } else if vol > 0 && imbalance != best_imbalance {
            imbalance < best_imbalance
        } else if vol == 0 && best_price == 0 && p > 0 {
            false
        } else {
            false
        };
        if better {
            best_price = p;
            best_vol = vol;
            best_imbalance = imbalance;
        }
    }

    // Compute crossing capacities at best_price.
    let mut bid_rem: Vec<(usize, u128)> = orders
        .iter()
        .enumerate()
        .filter(|(_, o)| o.role == Side::Bid && o.crosses(best_price))
        .map(|(i, o)| (i, o.max_goods))
        .collect();
    let mut ask_rem: Vec<(usize, u128)> = orders
        .iter()
        .enumerate()
        .filter(|(_, o)| o.role == Side::Ask && o.crosses(best_price))
        .map(|(i, o)| (i, o.max_goods))
        .collect();

    let total_bid_cap: u128 = bid_rem.iter().map(|(_, q)| *q).sum();
    let total_ask_cap: u128 = ask_rem.iter().map(|(_, q)| *q).sum();

    // Two-pointer lot routing matching `DrexBatch.obend` (`route` / `pair`).
    let mut moves = Vec::new();
    let mut bi = 0usize;
    let mut ai = 0usize;
    while bi < bid_rem.len() && ai < ask_rem.len() {
        let (b_idx, b_q) = bid_rem[bi];
        let (a_idx, a_q) = ask_rem[ai];
        let matched = b_q.min(a_q);
        if matched > 0 {
            let bid_seat = orders[b_idx].seat;
            let ask_seat = orders[a_idx].seat;
            moves.push(Transfer {
                from: ask_seat,
                to: bid_seat,
                asset: market.goods,
                amount: matched,
            });
            let currency_amt = best_price.saturating_mul(matched);
            if currency_amt > 0 {
                moves.push(Transfer {
                    from: bid_seat,
                    to: ask_seat,
                    asset: market.currency,
                    amount: currency_amt,
                });
            }
        }
        bid_rem[bi].1 -= matched;
        ask_rem[ai].1 -= matched;
        if bid_rem[bi].1 == 0 {
            bi += 1;
        }
        if ask_rem[ai].1 == 0 {
            ai += 1;
        }
    }

    // Synthesize optimal dual potentials and per-order slacks with zero duality gap:
    // - When crossing asks are the bottleneck (total_ask_cap <= total_bid_cap), every crossing ask
    //   is 100% filled: choose π = (0, 1), slack(Bid) = 0, slack(Ask) = 2 -> c·s = 2*S = w·f.
    // - When crossing bids are the bottleneck (total_bid_cap < total_ask_cap), every crossing bid
    //   is 100% filled: choose π = (1, 0), slack(Bid) = 2, slack(Ask) = 0 -> c·s = 2*B = w·f.
    let (bid_potential, ask_potential) = if total_ask_cap <= total_bid_cap {
        (0i128, 1i128)
    } else {
        (1i128, 0i128)
    };
    let slacks: Vec<i128> = orders
        .iter()
        .map(|o| {
            let sign = o.role.out();
            let pi_a = bid_potential * sign + ask_potential * (-sign);
            (1 - pi_a).max(0)
        })
        .collect();

    let cert = Certificate {
        price: best_price,
        bid_potential,
        ask_potential,
        slacks: slacks.clone(),
    };

    // Self-verify against the exact kernel judge before returning.
    verify_cert_f(market, orders, &moves, &cert)?;

    let mut fills = Vec::with_capacity(orders.len());
    let mut primal_objective = 0i128;
    let mut dual_objective = 0i128;
    for (j, o) in orders.iter().enumerate() {
        let crosses = o.crosses(best_price);
        let capacity = if crosses { o.max_goods } else { 0 };
        let fill_i = o.fill(&moves, market);
        let paid_i = o.paid(&moves, market);
        let slack = slacks[j];
        primal_objective = primal_objective.saturating_add(fill_i);
        dual_objective = dual_objective.saturating_add((capacity as i128).saturating_mul(slack));
        fills.push(OrderFill {
            seat: o.seat,
            role: o.role,
            limit_price: o.limit_price,
            max_goods: o.max_goods,
            crosses,
            capacity,
            fill: fill_i.max(0) as u128,
            paid: paid_i.max(0) as u128,
            slack,
        });
    }
    let duality_gap = dual_objective.saturating_sub(primal_objective);

    Ok(ClearingSolution {
        market: market.clone(),
        orders: orders.to_vec(),
        moves,
        cert,
        fills,
        volume: best_vol,
        primal_objective,
        dual_objective,
        duality_gap,
    })
}

fn parse_u64_val(v: &Value, field: &str) -> Result<u64> {
    if let Some(n) = v.as_u64() {
        return Ok(n);
    }
    if let Some(s) = v.as_str() {
        return s
            .trim()
            .parse::<u64>()
            .map_err(|_| format!("{field}: expected u64, got `{s}`").into());
    }
    Err(format!("{field}: expected integer").into())
}

fn parse_u128_val(v: &Value, field: &str) -> Result<u128> {
    if let Some(n) = v.as_u64() {
        return Ok(u128::from(n));
    }
    if let Some(s) = v.as_str() {
        return s
            .trim()
            .parse::<u128>()
            .map_err(|_| format!("{field}: expected non-negative integer, got `{s}`").into());
    }
    Err(format!("{field}: expected non-negative integer").into())
}

fn extract_leg(v: &Value, field: &str) -> Result<(u64, u128)> {
    let leg = if let Some(arr) = v.as_array() {
        if arr.len() != 1 {
            return Err(format!("{field}: expected single-asset leg").into());
        }
        &arr[0]
    } else {
        v
    };
    let asset = parse_u64_val(
        leg.get("asset").ok_or_else(|| format!("{field}: missing `asset`"))?,
        "asset",
    )?;
    let amount = parse_u128_val(
        leg.get("amount").ok_or_else(|| format!("{field}: missing `amount`"))?,
        "amount",
    )?;
    Ok((asset, amount))
}

fn parse_order_json(market: &Market, v: &Value, default_role: Option<Side>) -> Result<Order> {
    let seat_val = v
        .get("seat")
        .or_else(|| v.get("account"))
        .or_else(|| v.get("id"))
        .ok_or("order missing `seat` (or `account`)")?;
    let seat = parse_u64_val(seat_val, "seat")?;

    // Check if `give` and `want` are provided directly.
    if let (Some(give_v), Some(want_v)) = (v.get("give"), v.get("want")) {
        let (give_asset, give_amount) = extract_leg(give_v, "give")?;
        let (want_asset, want_amount) = extract_leg(want_v, "want")?;
        return Order::from_give_want(market, seat, give_asset, give_amount, want_asset, want_amount);
    }

    let role = if let Some(r_val) = v.get("role").or_else(|| v.get("side")) {
        let r_str = r_val.as_str().ok_or("order `role` must be a string (`bid` or `ask`)")?;
        Side::parse(r_str)?
    } else if let Some(r) = default_role {
        r
    } else {
        return Err(format!("seat {seat}: order missing `role` (`bid` or `ask`)").into());
    };

    let qty_val = v
        .get("max_goods")
        .or_else(|| v.get("maxGoods"))
        .or_else(|| v.get("qty"))
        .or_else(|| v.get("quantity"))
        .or_else(|| v.get("amount"))
        .ok_or_else(|| format!("seat {seat}: order missing `max_goods` (or `qty`)"))?;
    let max_goods = parse_u128_val(qty_val, "max_goods")?;
    if max_goods == 0 {
        return Err(format!("seat {seat}: max_goods must be > 0").into());
    }

    if let Some(total_val) = v.get("total") {
        let total = parse_u128_val(total_val, "total")?;
        let limit_price = match role {
            Side::Bid => total / max_goods,
            Side::Ask => total.div_ceil(max_goods),
        };
        return Ok(Order {
            seat,
            role,
            limit_price,
            max_goods,
            total,
        });
    }

    let price_val = v
        .get("limit_price")
        .or_else(|| v.get("limitPrice"))
        .or_else(|| v.get("price"))
        .ok_or_else(|| format!("seat {seat}: order missing `limit_price` (or `price`)"))?;
    let limit_price = parse_u128_val(price_val, "limit_price")?;

    Ok(match role {
        Side::Bid => Order::bid(seat, limit_price, max_goods),
        Side::Ask => Order::ask(seat, limit_price, max_goods),
    })
}

/// Parse a JSON string (either an array of orders or an object `{"market": ..., "orders": [...]}`)
/// into `(Market, Vec<Order>)`.
pub(crate) fn parse_orders_json(input: &str) -> Result<(Market, Vec<Order>)> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Err("orders JSON cannot be empty".into());
    }
    let root: Value = serde_json::from_str(trimmed).map_err(|e| format!("invalid orders JSON: {e}"))?;
    let mut market = Market::default();
    if let Some(m) = root.get("market").or_else(|| root.value_market()) {
        if let Some(c) = m.get("currency") {
            market.currency = parse_u64_val(c, "market.currency")?;
        }
        if let Some(g) = m.get("goods") {
            market.goods = parse_u64_val(g, "market.goods")?;
        }
        if let Some(e) = m.get("epsilon") {
            market.epsilon = parse_u128_val(e, "market.epsilon")?;
        }
    }

    let mut orders = Vec::new();
    if let Some(arr) = root.as_array() {
        for item in arr {
            orders.push(parse_order_json(&market, item, None)?);
        }
    } else if let Some(arr) = root.get("orders").and_then(Value::as_array) {
        for item in arr {
            orders.push(parse_order_json(&market, item, None)?);
        }
    } else {
        let mut found = false;
        if let Some(bids) = root.get("bids").and_then(Value::as_array) {
            found = true;
            for item in bids {
                orders.push(parse_order_json(&market, item, Some(Side::Bid))?);
            }
        }
        if let Some(asks) = root.get("asks").and_then(Value::as_array) {
            found = true;
            for item in asks {
                orders.push(parse_order_json(&market, item, Some(Side::Ask))?);
            }
        }
        if !found {
            return Err("expected JSON array of orders or object with `orders` / `bids`+`asks`".into());
        }
    }

    Ok((market, orders))
}

trait ValueMarketExt {
    fn value_market(&self) -> Option<&Value>;
}

impl ValueMarketExt for Value {
    fn value_market(&self) -> Option<&Value> {
        if self.is_object() && (self.get("currency").is_some() || self.get("goods").is_some()) {
            Some(self)
        } else {
            None
        }
    }
}

/// Parse human-friendly order specifications (`seat:limit_price:qty` or `seat:role:limit_price:qty`,
/// separated by commas, semicolons, or newlines) for a given default `Side`.
pub(crate) fn parse_human_orders(input: &str, default_side: Side) -> Result<Vec<Order>> {
    let mut out = Vec::new();
    for raw in input
        .split([',', ';', '\n'])
        .map(str::trim)
        .filter(|s| !s.is_empty())
    {
        let parts: Vec<&str> = raw.split(':').map(str::trim).collect();
        let (seat_s, role, price_s, qty_s) = match parts.as_slice() {
            [seat_s, price_s, qty_s] => (*seat_s, default_side, *price_s, *qty_s),
            [seat_s, role_s, price_s, qty_s] => (*seat_s, Side::parse(role_s)?, *price_s, *qty_s),
            _ => {
                return Err(format!(
                    "invalid order entry `{raw}` (expected `seat:limit_price:qty`, e.g. `10:5:3`)"
                )
                .into())
            }
        };
        let seat: u64 = seat_s
            .parse()
            .map_err(|_| format!("invalid seat `{seat_s}` in `{raw}`"))?;
        let limit_price: u128 = price_s
            .parse()
            .map_err(|_| format!("invalid limit_price `{price_s}` in `{raw}`"))?;
        let max_goods: u128 = qty_s
            .parse()
            .map_err(|_| format!("invalid qty `{qty_s}` in `{raw}`"))?;
        if max_goods == 0 {
            return Err(format!("seat {seat}: qty must be > 0 in `{raw}`").into());
        }
        out.push(match role {
            Side::Bid => Order::bid(seat, limit_price, max_goods),
            Side::Ask => Order::ask(seat, limit_price, max_goods),
        });
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cert_f_solver_matches_lean_sample_orders_and_rejects_manipulations() {
        let market = Market {
            currency: 1,
            goods: 2,
            epsilon: 0,
        };
        let orders = vec![
            Order::bid(10, 5, 3), // gives 15 currency, wants 3 goods
            Order::bid(11, 4, 2), // gives 8 currency, wants 2 goods
            Order::ask(20, 3, 2), // gives 2 goods, wants 6 currency
            Order::ask(21, 4, 3), // gives 3 goods, wants 12 currency
        ];
        let sol = solve_clearing(&market, &orders).expect("solve sample book");
        assert_eq!(sol.cert.price, 4);
        assert_eq!(sol.volume, 5);
        assert_eq!(sol.cert.bid_potential, 0);
        assert_eq!(sol.cert.ask_potential, 1);
        assert_eq!(sol.cert.slacks, vec![0, 0, 2, 2]);
        assert_eq!(sol.duality_gap, 0);

        // Verify self-verifier accepts the honest solution.
        verify_cert_f(&market, &orders, &sol.moves, &sol.cert).expect("honest cert must verify");

        // 1. Under-clearing (leaving crossable volume on the table with same duals) must fail dualityGap.
        let partial_moves = vec![
            Transfer { from: 20, to: 10, asset: 2, amount: 2 },
            Transfer { from: 10, to: 20, asset: 1, amount: 8 },
        ];
        let err = verify_cert_f(&market, &orders, &partial_moves, &sol.cert).unwrap_err();
        assert!(err.to_string().contains("dualityGap"), "expected dualityGap error, got: {err}");

        // 2. Non-uniform price transfer must fail notUniform.
        let mut bad_uniform = sol.moves.clone();
        bad_uniform[1].amount += 1;
        let err = verify_cert_f(&market, &orders, &bad_uniform, &sol.cert).unwrap_err();
        assert!(err.to_string().contains("notUniform"), "expected notUniform error, got: {err}");

        // 3. Negative slack must fail dualSlackNeg.
        let mut bad_slack = sol.cert.clone();
        bad_slack.slacks[0] = -1;
        let err = verify_cert_f(&market, &orders, &sol.moves, &bad_slack).unwrap_err();
        assert!(err.to_string().contains("dualSlackNeg"), "expected dualSlackNeg error, got: {err}");
    }

    #[test]
    fn cert_f_solver_handles_asymmetric_bid_and_ask_bottlenecks() {
        let market = Market::default();
        // Case A: Bid bottleneck (total crossing bid = 4 < total crossing ask = 7 at price 10).
        let orders_bid_bottleneck = vec![
            Order::bid(1, 12, 4),
            Order::bid(2, 8, 5), // does not cross price 10
            Order::ask(3, 9, 3),
            Order::ask(4, 10, 4),
        ];
        let sol_a = solve_clearing(&market, &orders_bid_bottleneck).expect("solve bid bottleneck");
        assert_eq!(sol_a.cert.price, 10);
        assert_eq!(sol_a.volume, 4);
        assert_eq!(sol_a.cert.bid_potential, 1);
        assert_eq!(sol_a.cert.ask_potential, 0);
        assert_eq!(sol_a.duality_gap, 0);
        verify_cert_f(&market, &orders_bid_bottleneck, &sol_a.moves, &sol_a.cert).unwrap();

        // Case B: Ask bottleneck (total crossing ask = 3 < total crossing bid = 6 at price 10).
        let orders_ask_bottleneck = vec![
            Order::bid(1, 12, 3),
            Order::bid(2, 10, 3),
            Order::ask(3, 9, 3),
            Order::ask(4, 15, 5), // does not cross price 10
        ];
        let sol_b = solve_clearing(&market, &orders_ask_bottleneck).expect("solve ask bottleneck");
        assert_eq!(sol_b.volume, 3);
        assert_eq!(sol_b.cert.bid_potential, 0);
        assert_eq!(sol_b.cert.ask_potential, 1);
        assert_eq!(sol_b.duality_gap, 0);
        verify_cert_f(&market, &orders_ask_bottleneck, &sol_b.moves, &sol_b.cert).unwrap();
    }

    #[test]
    fn parse_orders_json_and_human_syntax_round_trip() {
        let json_in = r#"[
            {"seat": 10, "role": "bid", "limit_price": 5, "max_goods": 3},
            {"seat": 11, "role": "bid", "give": {"asset": 1, "amount": 8}, "want": {"asset": 2, "amount": 2}},
            {"seat": 20, "role": "ask", "limit_price": 3, "max_goods": 2},
            {"seat": 21, "role": "ask", "limit_price": 4, "max_goods": 3}
        ]"#;
        let (market, orders) = parse_orders_json(json_in).unwrap();
        let sol = solve_clearing(&market, &orders).unwrap();
        assert_eq!(sol.cert.price, 4);
        assert_eq!(sol.volume, 5);

        let mut human_orders = parse_human_orders("10:5:3, 11:4:2", Side::Bid).unwrap();
        human_orders.extend(parse_human_orders("20:3:2\n21:4:3", Side::Ask).unwrap());
        let sol2 = solve_clearing(&market, &human_orders).unwrap();
        assert_eq!(sol2.to_json(), sol.to_json());

        let action = &sol.to_json()["seatInvokeAction"];
        assert_eq!(action["action"], "clear");
        assert_eq!(action["fills"].as_array().unwrap().len(), 4);
        assert_eq!(action["price"], 4);
        assert_eq!(action["certificate"]["price"], 4);
        assert_eq!(action["moves"][0]["source"], 20);
        assert_eq!(action["moves"][0]["destination"], 10);
    }

    #[test]
    fn verify_cert_f_rejects_duplicate_seats_and_invalid_transfer_directions() {
        let market = Market::default();
        let dup_orders = vec![Order::bid(10, 5, 3), Order::ask(10, 3, 3)];
        let err = solve_clearing(&market, &dup_orders).unwrap_err();
        assert!(err.contains("duplicate seat"), "expected duplicate seat, got: {err}");
        let v_err = verify_cert_f(
            &market,
            &dup_orders,
            &[],
            &Certificate {
                price: 4,
                bid_potential: 0,
                ask_potential: 1,
                slacks: vec![0, 0],
            },
        )
        .unwrap_err();
        assert!(v_err.to_string().contains("duplicateSeat"), "got: {v_err}");

        let orders = vec![Order::bid(10, 5, 2), Order::ask(20, 4, 2)];
        let sol = solve_clearing(&market, &orders).unwrap();

        // Zero-amount transfer must be rejected.
        let mut zero_moves = sol.moves.clone();
        zero_moves.push(Transfer {
            from: 20,
            to: 10,
            asset: 2,
            amount: 0,
        });
        let err = verify_cert_f(&market, &orders, &zero_moves, &sol.cert).unwrap_err();
        assert!(err.to_string().contains("zeroTransfer"), "got: {err}");

        // Self-transfer must be rejected.
        let self_moves = vec![Transfer {
            from: 10,
            to: 10,
            asset: 1,
            amount: 5,
        }];
        let err = verify_cert_f(&market, &orders, &self_moves, &sol.cert).unwrap_err();
        assert!(err.to_string().contains("selfTransfer"), "got: {err}");

        // Backwards goods flow (Bid -> Ask) must be rejected.
        let backwards_moves = vec![Transfer {
            from: 10,
            to: 20,
            asset: 2,
            amount: 2,
        }];
        let err = verify_cert_f(&market, &orders, &backwards_moves, &sol.cert).unwrap_err();
        assert!(err.to_string().contains("movesConsistent"), "got: {err}");
    }
}
