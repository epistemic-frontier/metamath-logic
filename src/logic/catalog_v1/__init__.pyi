from collections.abc import Iterator
from dataclasses import dataclass

@dataclass(frozen=True, slots=True)
class DeclarationHandle:
    declaration_id: str
    canonical_label: str
    kind: str
    source_ordinal: int
    interface_digest: str
    public_module: str
    declared_provider_id: str
    selected_provider_id: str
    selected_artifact_id: str
    provider_resolution_digest: str
    public_artifact_id: str
    public_entrypoint_contract: str
    public_entrypoint_reference: str

def by_label(label: str) -> DeclarationHandle: ...
def by_id(declaration_id: str) -> DeclarationHandle: ...
def iter_declarations() -> Iterator[DeclarationHandle]: ...
def count() -> int: ...
