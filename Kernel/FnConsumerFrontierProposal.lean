/- Exact gateway signing requests for the two ordered progress families. -/
import Kernel.FnConsumerFrontierGateway
import Kernel.FnSelectedPollCoverage
import Kernel.FnEmptyPollProgressV2

namespace Minidregg.Kernel.FnConsumerFrontierProposal

def selected (ingress : FnSelectedPollCoverage.Ingress) :
    FnConsumerFrontierGateway.Proposal :=
  { domain := ingress.spec.domain
    semantics := ingress.spec.semantics
    application := ingress.spec.evidence.key.application
    subject := ingress.spec.gatewaySubject
    target := ingress.spec.gatewayTarget
    capability := ingress.spec.gatewayCapability
    canonicalSpec := FnSelectedPollCoverage.specCodec.encode ingress.spec
    expectedAuthorityRoot := ingress.expectedAuthorityRoot
    expectedTargetRoot := ingress.expectedTargetRoot }

def empty (ingress : FnEmptyPollProgressV2.Ingress) :
    FnConsumerFrontierGateway.Proposal :=
  { domain := ingress.spec.domain
    semantics := ingress.spec.semantics
    application := ingress.spec.evidence.key.application
    subject := ingress.spec.gatewaySubject
    target := ingress.spec.gatewayTarget
    capability := ingress.spec.gatewayCapability
    canonicalSpec := FnEmptyPollProgressV2.specCodec.encode ingress.spec
    expectedAuthorityRoot := ingress.expectedAuthorityRoot
    expectedTargetRoot := ingress.expectedTargetRoot }

end Minidregg.Kernel.FnConsumerFrontierProposal
