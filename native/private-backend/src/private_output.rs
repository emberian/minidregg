//! Actual fixed-recipient reconstruction of completed shared Boolean outputs.
//! This is a private OUTPUT precursor, not successor resharing: the designated
//! recipient learns the result. Fresh current-source ReleaseAdmission and
//! allAppliedReady must authorize honest delivery requests in the native join.
//! Low-level environment requests supply no grant, Native Qualified or GOD.
use crate::{
    acss_id,
    codec::{bad, bytes, Correlation, Generation, Journal, Nat, Purpose, Reader},
    consensus_wire::Cursor,
    custody::{self, hash},
    field_network::fields,
    field_network_layers::LayerEngine,
    private_send::{self, PrivateSend},
    private_send_store,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    io::Result,
    path::Path,
};
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Message {
    pub context: [u8; 32],
    pub dealer: u16,
    pub message: private_send::Message,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Send {
    pub to: u16,
    pub message: Message,
}
#[derive(Clone)]
pub struct RecipientResult {
    context: [u8; 32],
    generation: Generation,
    recipient: u16,
    descriptor: Vec<u8>,
    bits: Vec<bool>,
}
impl RecipientResult {
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn generation(&self) -> &Generation {
        &self.generation
    }
    pub fn recipient(&self) -> u16 {
        self.recipient
    }
    pub fn descriptor_bytes(&self) -> &[u8] {
        &self.descriptor
    }
    /// Plaintext ONLY at the selected recipient. Source-current publication or
    /// exporting to another audience requires its separate current release grant.
    pub fn bits(&self) -> &[bool] {
        &self.bits
    }
}
#[derive(Clone)]
pub struct PrivateOutput {
    me: u16,
    n: usize,
    f: usize,
    generation: Generation,
    context: [u8; 32],
    parent_context: [u8; 32],
    recipient: u16,
    descriptor: Vec<u8>,
    count: usize,
    local_shares: Vec<crate::reconstruction::Field>,
    burn_prefix: Journal,
    deliveries: Vec<PrivateSend>,
    started: bool,
    requested: bool,
    rejected: BTreeSet<u16>,
    result: Option<RecipientResult>,
    invalid_result: bool,
}
impl PrivateOutput {
    /// PUBLIC context/shape/recipient preflight, one-use reservation + fsync and
    /// actual anchor readback precede the completed output's FIRST share getter.
    /// Native must separately authorize exact descriptor/current recipient/funds.
    pub fn reserve(
        parent: &LayerEngine,
        recipient: u16,
        descriptor: &[u8],
        anchor: &Path,
        local: &Path,
    ) -> Result<Self> {
        let (n, f) = parent.roster();
        let me = parent.holder();
        let generation = parent.plan().generation.clone();
        let count = parent.plan().network.outputs.len();
        if parent.output().is_none()
            || parent.failure().is_some()
            || recipient as usize >= n
            || descriptor.is_empty()
            || descriptor.len() > 65536
            || count == 0
            || count > 4092
        {
            return Err(bad("actual completed output/recipient/descriptor capacity"));
        }
        let mut binding = b"DREGG.PRIVATE.OUTPUT\x01".to_vec();
        generation.put(&mut binding);
        binding.extend(parent.context());
        binding.extend(recipient.to_le_bytes());
        bytes(descriptor, &mut binding);
        Nat::new(n as u64).put(&mut binding);
        Nat::new(f as u64).put(&mut binding);
        Nat::new(count as u64).put(&mut binding);
        let context = hash(&binding);
        // Stable ID excludes descriptor/credential randomness so replacing an
        // output descriptor cannot reserve the SAME result-to-recipient again.
        let mut identity = b"DREGG.PRIVATE.OUTPUT.ONE.USE\x01".to_vec();
        identity.extend(parent.context());
        identity.extend(recipient.to_le_bytes());
        let id = Correlation {
            pool: Nat::from_be(&hash(&identity)),
            row: Nat::new(0),
        };
        let _guard = custody::lock(&local.with_extension("output.lock"))?;
        let before = Journal::decode(&custody::rpc(anchor, &[0])?)?;
        before.reserve(id.clone(), generation.clone(), Purpose::HolderPad)?;
        let mut req = vec![1];
        req.extend(crate::codec::request(&id, &generation, Purpose::HolderPad));
        let confirmed = Journal::decode(&custody::rpc(anchor, &req)?)?;
        if !confirmed.extends(&before)
            || !confirmed.preserves_allocations(&before)
            || !confirmed.allocations.iter().any(|a| {
                a.id == id
                    && a.generation == generation
                    && a.purpose == Purpose::HolderPad
                    && !a.consumed
            })
        {
            return Err(bad("private output actual anchor retention"));
        }
        let mut receipt = b"DREGG.PRIVATE.OUTPUT.BURN\x01".to_vec();
        bytes(&binding, &mut receipt);
        bytes(&confirmed.encode(), &mut receipt);
        custody::snapshot(local, &receipt)?;
        if std::fs::read(local)? != receipt {
            return Err(bad("private output durable readback"));
        }
        let latest = Journal::decode(&custody::rpc(anchor, &[0])?)?;
        if !latest.extends(&confirmed) || !latest.preserves_allocations(&confirmed) {
            return Err(bad("private output anchor regression"));
        }
        let output = parent.output().unwrap();
        if output.context() != parent.context()
            || output.holder() != me
            || output.shares().len() != count
        {
            return Err(bad("actual output share binding"));
        }
        let shares = output.shares().to_vec();
        Self::initial(
            me,
            n,
            f,
            generation,
            context,
            parent.context(),
            recipient,
            descriptor.to_vec(),
            count,
            shares,
            confirmed,
        )
    }
    fn initial(
        me: u16,
        n: usize,
        f: usize,
        g: Generation,
        context: [u8; 32],
        parent: [u8; 32],
        recipient: u16,
        descriptor: Vec<u8>,
        count: usize,
        shares: Vec<crate::reconstruction::Field>,
        burn_prefix: Journal,
    ) -> Result<Self> {
        let mut binding = b"DREGG.PRIVATE.OUTPUT\x01".to_vec();
        g.put(&mut binding);
        binding.extend(parent);
        binding.extend(recipient.to_le_bytes());
        bytes(&descriptor, &mut binding);
        for v in [n, f, count] {
            Nat::new(v as u64).put(&mut binding);
        }
        if hash(&binding) != context {
            return Err(bad("output exact public descriptor binding"));
        }
        let mut child = g.clone();
        child.invocation = Nat::from_be(&context);
        let length = 32 + 2 + 2 + count * 16;
        let deliveries = (0..n)
            .map(|d| PrivateSend::new(me, d as u16, n, f, &child, length))
            .collect::<Result<Vec<_>>>()?;
        Ok(Self {
            me,
            n,
            f,
            generation: g,
            context,
            parent_context: parent,
            recipient,
            descriptor,
            count,
            local_shares: shares,
            burn_prefix,
            deliveries,
            started: false,
            requested: false,
            rejected: BTreeSet::new(),
            result: None,
            invalid_result: false,
        })
    }
    pub fn holder(&self) -> u16 {
        self.me
    }
    pub fn roster(&self) -> (usize, usize) {
        (self.n, self.f)
    }
    pub fn generation(&self) -> &Generation {
        &self.generation
    }
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
    pub fn recipient(&self) -> u16 {
        self.recipient
    }
    pub fn result(&self) -> Option<&RecipientResult> {
        self.result.as_ref()
    }
    pub fn rejected_holders(&self) -> &BTreeSet<u16> {
        &self.rejected
    }
    pub fn invalid_result(&self) -> bool {
        self.invalid_result
    }
    fn packets(&self, dealer: u16, ps: Vec<private_send::Send>) -> Vec<Send> {
        ps.into_iter()
            .map(|p| Send {
                to: p.to,
                message: Message {
                    context: self.context,
                    dealer,
                    message: p.message,
                },
            })
            .collect()
    }
    pub fn start_with_coefficients(
        &mut self,
        coeff: &[Vec<crate::reconstruction::Field>],
    ) -> Result<Vec<Send>> {
        if self.started {
            return Err(bad(
                "output sender repeated; replay original durable outbox",
            ));
        }
        let mut plain = self.context.to_vec();
        plain.extend(self.me.to_le_bytes());
        plain.extend(self.recipient.to_le_bytes());
        for x in &self.local_shares {
            plain.extend(x.0.to_le_bytes());
        }
        let ps = self.deliveries[self.me as usize].dealer_with_coefficients(&plain, coeff)?;
        self.started = true;
        Ok(self.packets(self.me, ps))
    }
    /// Explicit SOURCE ENVIRONMENT request, never a network-supplied grant/Bool.
    /// Native must require fresh current output release and allAppliedReady.
    pub fn request_delivery(&mut self) -> Result<Vec<Send>> {
        if self.requested {
            return Ok(vec![]);
        }
        self.requested = true;
        let mut out = vec![];
        for d in 0..self.n {
            let ps = self.deliveries[d].request_delivery(self.recipient)?;
            out.extend(self.packets(d as u16, ps));
        }
        out.extend(self.progress()?);
        Ok(out)
    }
    pub fn receive(&mut self, sender: u16, m: Message) -> Result<Vec<Send>> {
        if sender as usize >= self.n || m.dealer as usize >= self.n || m.context != self.context {
            return Err(bad("output sender/context"));
        }
        match &m.message.body {
            private_send::Body::Request { receiver, .. }
            | private_send::Body::Transfer { receiver, .. }
                if *receiver != self.recipient =>
            {
                return Err(bad("output cross-recipient request/transfer"))
            }
            _ => {}
        }
        let d = m.dealer;
        let ps = self.deliveries[d as usize].receive(sender, m.message)?;
        let mut out = self.packets(d, ps);
        out.extend(self.progress()?);
        Ok(out)
    }
    fn progress(&mut self) -> Result<Vec<Send>> {
        if self.me != self.recipient || self.result.is_some() || self.invalid_result {
            return Ok(vec![]);
        }
        let mut points = BTreeMap::new();
        for d in 0..self.n {
            let Some(plain) = self.deliveries[d].delivered.as_ref() else {
                continue;
            };
            // A malformed corrupt-dealer plaintext is retained/rejected, not an error
            // that rolls back completed honest ciphertext/agreement state.
            let good = plain.len() == 36 + 16 * self.count
                && plain[..32] == self.context
                && u16::from_le_bytes(plain[32..34].try_into().unwrap()) == d as u16
                && u16::from_le_bytes(plain[34..36].try_into().unwrap()) == self.recipient;
            if !good {
                self.rejected.insert(d as u16);
                continue;
            }
            points.insert(d as u16, fields(&plain[36..], self.count)?);
        }
        if let Some((polys, _)) =
            acss_id::correct_polynomials(&points, self.f, self.n - self.f, self.count)?
        {
            let values = polys.iter().map(|p| p[0]).collect::<Vec<_>>();
            if values.iter().any(|v| v.0 > 1) {
                self.invalid_result = true;
            } else {
                self.result = Some(RecipientResult {
                    context: self.context,
                    generation: self.generation.clone(),
                    recipient: self.recipient,
                    descriptor: self.descriptor.clone(),
                    bits: values.iter().map(|v| v.0 == 1).collect(),
                });
            }
        }
        Ok(vec![])
    }
    pub(crate) fn initial_bytes(&self) -> Result<Vec<u8>> {
        if self.started || self.requested || self.result.is_some() {
            return Err(bad("output original initialization only"));
        }
        let mut b = b"DREGG.PRIVATE.OUTPUT.INITIAL\x01".to_vec();
        self.generation.put(&mut b);
        b.extend(self.context);
        b.extend(self.parent_context);
        b.extend(self.me.to_le_bytes());
        b.extend(self.recipient.to_le_bytes());
        for n in [self.n, self.f, self.count] {
            Nat::new(n as u64).put(&mut b);
        }
        bytes(&self.descriptor, &mut b);
        bytes(&self.burn_prefix.encode(), &mut b);
        for x in &self.local_shares {
            b.extend(x.0.to_le_bytes());
        }
        Ok(b)
    }
    pub(crate) fn restore_initial(
        b: &[u8],
        expected_generation: &Generation,
        expected_context: [u8; 32],
        me: u16,
        recipient: u16,
        anchor: &Path,
    ) -> Result<Self> {
        let frame = b"DREGG.PRIVATE.OUTPUT.INITIAL\x01";
        if !b.starts_with(frame) {
            return Err(bad("output initial frame"));
        }
        let mut r = Reader::new(&b[frame.len()..])?;
        let g = Generation::get(&mut r)?;
        // Reader has no fixed-byte method; canonical remainder is parsed by Cursor.
        // Exact canonical generation prefix supplies its own consumed length.
        let mut gb = vec![];
        g.put(&mut gb);
        let mut c = Cursor::new(&b[frame.len() + gb.len()..])?;
        let context = c.fixed32()?;
        let parent = c.fixed32()?;
        let holder = c.u16()?;
        let target = c.u16()?;
        fn nat(c: &mut Cursor) -> Result<usize> {
            let mut b = vec![];
            loop {
                let v = c.byte()?;
                b.push(v);
                if v == 255 {
                    break;
                }
            }
            let mut r = Reader::new(&b)?;
            let n = usize::try_from(r.nat()?.value()?).map_err(|_| bad("output Nat capacity"))?;
            r.finish()?;
            Ok(n)
        }
        let n = nat(&mut c)?;
        let f = nat(&mut c)?;
        let count = nat(&mut c)?;
        let descriptor = c.bytes()?;
        let burn = Journal::decode(&c.bytes()?)?;
        if &g != expected_generation
            || context != expected_context
            || holder != me
            || target != recipient
            || f == 0
            || f > 5
            || n != 3 * f + 1
            || me as usize >= n
            || recipient as usize >= n
            || count == 0
            || count > 4092
            || descriptor.is_empty()
            || descriptor.len() > 65536
        {
            return Err(bad("output original generation/holder/recipient/capacity"));
        }
        let shares = fields(c.take(count * 16)?, count)?;
        c.finish()?;
        let latest = Journal::decode(&custody::rpc(anchor, &[0])?)?;
        let mut id = b"DREGG.PRIVATE.OUTPUT.ONE.USE\x01".to_vec();
        id.extend(parent);
        id.extend(recipient.to_le_bytes());
        let id = Correlation {
            pool: Nat::from_be(&hash(&id)),
            row: Nat::new(0),
        };
        if !latest.extends(&burn)
            || !latest.preserves_allocations(&burn)
            || !burn.allocations.iter().any(|a| {
                a.id == id && a.generation == g && a.purpose == Purpose::HolderPad && !a.consumed
            })
        {
            return Err(bad("output retained anchor before recovery"));
        }
        let state = Self::initial(
            me, n, f, g, context, parent, recipient, descriptor, count, shares, burn,
        )?;
        if state.initial_bytes()? != b {
            return Err(bad("output initial canonical"));
        }
        Ok(state)
    }
}
pub fn encode_message(m: &Message) -> Vec<u8> {
    let mut b = b"DREGG.PRIVATE.OUTPUT.WIRE\x01".to_vec();
    b.extend(m.context);
    b.extend(m.dealer.to_le_bytes());
    bytes(&private_send_store::encode_message(&m.message), &mut b);
    b
}
pub fn decode_message(b: &[u8]) -> Result<Message> {
    let tag = b"DREGG.PRIVATE.OUTPUT.WIRE\x01";
    let mut c = Cursor::new(b)?;
    if c.take(tag.len())? != tag {
        return Err(bad("output wire frame"));
    }
    let m = Message {
        context: c.fixed32()?,
        dealer: c.u16()?,
        message: private_send_store::decode_message(&c.bytes()?)?,
    };
    c.finish()?;
    if encode_message(&m) != b {
        return Err(bad("output wire canonical"));
    }
    Ok(m)
}
