::  market.hoon: order matching v1, MUD §2.8
::  TEXT, NOT COMPILED: pseudocode for the NOCK lanes. Sample layout and key convention: programs/README.md.
::
::  sample   [ctx=[height=@ caller=@ room=@ now=@] inv=(list [key=@t val=@s])]
::           '0/N'  the order book {REALM}-market-{K} (market/fields.json: 1 seq; order k at 16+8k:
::                  +0 side (0 none, 1 buy, 2 sell), +1 asset, +2 qty, +3 price, +4 who, +5 filled, +6 open)
::           'r/I/F'  new escrow receipts since the runner's cursor, I = 0.., F: 0 side 1 asset 2 qty 3 price
::                  4 who. ASSUMED: the runner reads these from A_mkt's signed Book history (M8's send with
::                  topic sell/PRICE or buy/KIND/N/PRICE). They are NOT kernel-sampled inputs today, because
::                  a Book row is not a cell field. That is why this program is accountable (level 1) until
::                  K-BOOK-SLOTS.
::  product  a list of writes to the order book, AND (outside Nock) the runner's Book batch of out-transfers:
::           each fill = [asset -> buyer qty] + [gold -> seller qty*price], one Batch (atomic on the way out)
::  output law (grammar), law.market:
::    1 writer   subject == {MKT}
::    3 seq      field seq monotone
::    4..7 slot  side in {0,1,2}; open in {0,1}; leSlots field oK-filled field oK-qty; filled monotone unless
::               the slot is reused (who changed) or emptied (side 0)
::    after K-BOOK-SLOTS (MUD §2.8): every out-transfer joined to an in-transfer,
::      not (slot joint/target/{BOOK}/balance/{A_MKT}/{ASSET}/delta <= -(held+1))
::
::  v1 rule: price-time priority, one pass. A new sell at price p fills against open buys with price >= p,
::  oldest first, at the RESTING order's price. Any remainder takes a free slot. With no free slot the order
::  is refused and refunded (the Book batch returns the escrow). A partial fill leaves the slot open.
::
|=  [ctx=[height=@ caller=@ room=@ now=@] inv=(list [key=@t val=@s])]
^-  (list [key=@t val=@s])
|^
=/  book=(list order)  (turn (gulf 0 3) slot)
=/  new=(list order)   (receipts 0)
=|  out=(list [key=@t val=@s])
=/  seq  (get '0/1')
|-  ?~  new  (weld out ~[['0/1' seq]])
=/  o  i.new
=^  fills  book  (match o book)                        ::  fills: [slot qty] pairs against resting orders
=/  left  (sub qty.o (roll (turn fills tail) add))
=.  out  (weld out (fill-writes fills book))
=?  book  (gth left 0)  (rest o(qty left) book)         ::  the remainder rests in a free slot, or refunds
$(new t.new, seq (sum:si seq --1))
::
+$  order  [side=@ asset=@ qty=@ price=@ who=@ filled=@ open=@]
++  slot      |=(k=@ ^-(order (read-slot k)))         ::  reads '0/(16+8k)' .. '0/(22+8k)'
++  receipts  |=(i=@ ^-((list order) (read-receipts i)))
++  match                                              ::  opposite side, crossing price, oldest first
  |=  [o=order b=(list order)]
  ^-  [(list [@ @]) (list order)]
  !!                                                   ::  body left to the NOCK lane; the rule is above
++  fill-writes  |=([f=(list [@ @]) b=(list order)] ^-((list [key=@t val=@s]) !!))
++  rest         |=([o=order b=(list order)] ^-((list order) !!))
++  read-slot     |=(k=@ ^-(order !!))
++  read-receipts |=(i=@ ^-((list order) !!))
++  get
  |=  k=@t
  ^-  @s
  =/  l  inv
  |-  ?~  l  --0
  ?:  =(k key.i.l)  val.i.l
  $(l t.l)
--
