"""Typed, lazy Set.mm declaration catalog facade.

Importing this module performs no file or provider access and does not parse
the embedded facade.  The first API call validates all embedded canonical
bytes and then constructs immutable declaration handles.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Iterator
from dataclasses import dataclass
from typing import Any, NoReturn, cast

from ._embedded import (
    DECLARATION_COUNT,
    DISTRIBUTION_VERSION,
    FACADE_CANONICAL_BYTES,
    FACADE_CANONICAL_DIGEST,
    FACADE_DIGEST,
)

_DIGEST = re.compile(r"^sha256:[0-9a-f]{64}$")
_FACADE_SCHEMA = "setmm-release-facade-v1"
_DIGEST_DOMAIN = "setmm-release-facade-document-v1"


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


_ordered: tuple[DeclarationHandle, ...] | None = None
_by_id: dict[str, DeclarationHandle] | None = None
_by_label: dict[str, DeclarationHandle] | None = None


def _fail(message: str) -> NoReturn:
    raise RuntimeError("invalid embedded Set.mm release facade: " + message)


def _pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            _fail("duplicate object key")
        result[key] = value
    return result


def _canonical(value: object) -> bytes:
    try:
        return json.dumps(
            value,
            ensure_ascii=False,
            allow_nan=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    except (TypeError, ValueError, UnicodeEncodeError) as error:
        raise RuntimeError(
            "invalid embedded Set.mm release facade: non-canonical value"
        ) from error


def _object(value: object, fields: frozenset[str]) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != fields:
        _fail("object fields differ")
    return cast(dict[str, Any], value)


def _text(value: object) -> str:
    if not isinstance(value, str) or not value:
        _fail("expected non-empty text")
    return value


def _digest(value: object) -> str:
    text = _text(value)
    if _DIGEST.fullmatch(text) is None:
        _fail("expected SHA-256 digest")
    return text


def _ordinal(value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        _fail("expected nonnegative ordinal")
    return value


def _load() -> tuple[
    tuple[DeclarationHandle, ...],
    dict[str, DeclarationHandle],
    dict[str, DeclarationHandle],
]:
    global _ordered, _by_id, _by_label
    if _ordered is not None and _by_id is not None and _by_label is not None:
        return _ordered, _by_id, _by_label
    canonical_digest = (
        "sha256:" + hashlib.sha256(FACADE_CANONICAL_BYTES).hexdigest()
    )
    if canonical_digest != FACADE_CANONICAL_DIGEST:
        _fail("canonical byte digest differs")
    try:
        value = json.loads(
            FACADE_CANONICAL_BYTES.decode("utf-8"),
            object_pairs_hook=_pairs,
            parse_constant=lambda _token: _fail("unsupported number"),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise RuntimeError(
            "invalid embedded Set.mm release facade: strict JSON required"
        ) from error
    if _canonical(value) != FACADE_CANONICAL_BYTES:
        _fail("bytes are not canonical JSON")
    document = _object(
        value,
        frozenset(
            {
                "schema",
                "subject",
                "scope",
                "provider_authority",
                "release",
                "membership",
                "declaration_count",
                "declarations",
                "facade_digest",
            }
        ),
    )
    if document["schema"] != _FACADE_SCHEMA:
        _fail("schema differs")
    facade_digest = _digest(document["facade_digest"])
    if facade_digest != FACADE_DIGEST:
        _fail("declared facade digest differs")
    payload_document = dict(document)
    del payload_document["facade_digest"]
    payload = {
        "digest_domain": _DIGEST_DOMAIN,
        "document": payload_document,
    }
    computed_digest = "sha256:" + hashlib.sha256(_canonical(payload)).hexdigest()
    if computed_digest != facade_digest:
        _fail("facade self digest differs")
    release = _object(
        document["release"],
        frozenset(
            {
                "release_unit_id",
                "python_root",
                "distribution_name",
                "distribution_version",
                "kind",
            }
        ),
    )
    if release["distribution_version"] != DISTRIBUTION_VERSION:
        _fail("distribution version differs")
    declared_count = _ordinal(document["declaration_count"])
    declarations = document["declarations"]
    if (
        not isinstance(declarations, list)
        or declared_count != DECLARATION_COUNT
        or len(declarations) != DECLARATION_COUNT
        or DECLARATION_COUNT < 1
    ):
        _fail("declaration count differs")
    ordered: list[DeclarationHandle] = []
    by_id: dict[str, DeclarationHandle] = {}
    by_label: dict[str, DeclarationHandle] = {}
    for declaration_value in declarations:
        declaration = _object(
            declaration_value,
            frozenset(
                {
                    "declaration_id",
                    "canonical_label",
                    "kind",
                    "source_ordinal",
                    "interface_digest",
                    "public_module",
                    "provider_resolution",
                }
            ),
        )
        resolution = _object(
            declaration["provider_resolution"],
            frozenset(
                {
                    "declared_provider_id",
                    "selected_provider_id",
                    "selected_artifact_id",
                    "resolution_digest",
                    "public_artifact_id",
                    "public_entrypoint",
                }
            ),
        )
        endpoint = _object(
            resolution["public_entrypoint"],
            frozenset({"contract", "reference"}),
        )
        kind = _text(declaration["kind"])
        if kind not in {"$a", "$p"}:
            _fail("declaration kind differs")
        handle = DeclarationHandle(
            declaration_id=_text(declaration["declaration_id"]),
            canonical_label=_text(declaration["canonical_label"]),
            kind=kind,
            source_ordinal=_ordinal(declaration["source_ordinal"]),
            interface_digest=_digest(declaration["interface_digest"]),
            public_module=_text(declaration["public_module"]),
            declared_provider_id=_text(resolution["declared_provider_id"]),
            selected_provider_id=_text(resolution["selected_provider_id"]),
            selected_artifact_id=_text(resolution["selected_artifact_id"]),
            provider_resolution_digest=_digest(
                resolution["resolution_digest"]
            ),
            public_artifact_id=_text(resolution["public_artifact_id"]),
            public_entrypoint_contract=_text(endpoint["contract"]),
            public_entrypoint_reference=_text(endpoint["reference"]),
        )
        if handle.declaration_id in by_id:
            _fail("duplicate declaration ID")
        if handle.canonical_label in by_label:
            _fail("duplicate canonical label")
        ordered.append(handle)
        by_id[handle.declaration_id] = handle
        by_label[handle.canonical_label] = handle
    if tuple(item.declaration_id for item in ordered) != tuple(sorted(by_id)):
        _fail("declarations are not identity sorted")
    _ordered = tuple(ordered)
    _by_id = by_id
    _by_label = by_label
    return _ordered, _by_id, _by_label


def by_label(label: str) -> DeclarationHandle:
    """Return the immutable handle for one exact canonical label."""

    _, _, labels = _load()
    return labels[label]


def by_id(declaration_id: str) -> DeclarationHandle:
    """Return the immutable handle for one stable declaration identity."""

    _, identities, _ = _load()
    return identities[declaration_id]


def iter_declarations() -> Iterator[DeclarationHandle]:
    """Iterate declarations in stable identity order."""

    ordered, _, _ = _load()
    return iter(ordered)


def count() -> int:
    """Return the validated number of facade declarations."""

    ordered, _, _ = _load()
    return len(ordered)


__all__ = [
    "DeclarationHandle",
    "by_id",
    "by_label",
    "count",
    "iter_declarations",
]
