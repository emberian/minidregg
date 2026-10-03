# Station consumes the community's ONE source-version interface.
# CatalogReview.Candidate.source is currently generic exact source bytes; it is
# not silently renamed to Station artifactID. Native source publication must
# independently bind all three identities: source-package/compiled-program/public
# method export, and this separately supplied exact Station SourceVersion.
import Base
import ./SharedConsequences.bend as Station
import ./WorldCoauthoring.bend as Community

type RuleUse is Data:
  RuleUse{version: Community.VersionRef, stationSource: Station.SourceVersion,
    instance: Station.Ref}

# This is a typed declaration/reference, not an admitted conversion witness.
# Receiving retains actual source publication/adoption evidence separately.
def rule_use(version: Community.VersionRef, stationSource: Station.SourceVersion,
    instance: Station.Ref) -> RuleUse:
  RuleUse{version, stationSource, instance}

def version(use: RuleUse) -> Community.VersionRef:
  match use:
    case RuleUse{selected, stationSource, instance}:
      selected

def pinned_instance(use: RuleUse) -> Community.PinnedUse:
  match use:
    case RuleUse{version, stationSource, instance}:
      match instance:
        case Station.Ref{target, root}:
          Community.PinnedUse{target, root, version}

# Rule source updates do not change existing instance/version pins. Migration
# is independently authorized; preserving a list never creates native history.
def retained(uses: List<&2, Community.PinnedUse>) -> List<&2, Community.PinnedUse>:
  Community.preserve_uses(uses)

law complete_community_version_retained:
  for +selected: Community.VersionRef
  for stationSource: Station.SourceVersion
  for instance: Station.Ref
  {version(rule_use(selected, stationSource, instance)) == selected : Community.VersionRef}

def complete_community_version_retained(selected, stationSource, instance):
  {==}

law existing_instances_not_migrated:
  for +uses: List<&2, Community.PinnedUse>
  {retained(uses) == uses : List<&2, Community.PinnedUse>}

def existing_instances_not_migrated(uses):
  Community.preserved_uses_exact(uses)
