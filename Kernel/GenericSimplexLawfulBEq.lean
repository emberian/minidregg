import Kernel.GenericSimplex
import Theory.AssertAxioms

namespace Minidregg.Kernel.GenericSimplexLawfulBEq
open Minidregg.Kernel.GenericSimplex
/- The executable derived Boolean equality agrees with propositional equality;
needed when converting actual contains guards into retained event membership. -/
deriving instance ReflBEq for Kind
deriving instance LawfulBEq for Kind
deriving instance ReflBEq for Message
deriving instance LawfulBEq for Message
deriving instance ReflBEq for AuditEvent
deriving instance LawfulBEq for AuditEvent
#assert_axioms instLawfulBEqKind
#assert_axioms instLawfulBEqMessage
#assert_axioms instLawfulBEqAuditEvent
end Minidregg.Kernel.GenericSimplexLawfulBEq
