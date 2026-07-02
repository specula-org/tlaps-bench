"""triviality_audit.gate — drop vs audit behaviour.

A degenerate task (its ``PROOF OBVIOUS`` placeholder already verifies) must not
survive generation: the generators call ``gate(drop=True)`` so a fresh
generation self-heals instead of re-shipping the tasks a prior cleanup deleted.
These tests mock the (slow) tlapm scan and assert only the gate's file-level
contract — that a flagged task is deleted under ``drop`` and kept without it,
and the exit-code / manifest contract holds.

Run: PYTHONPATH=src python3 -m pytest tests/dataset/test_triviality_gate.py
"""

import json

from dataset import triviality_audit


def _make_tasks(tmp_path):
    good = tmp_path / "Good_Thm.tla"
    bad = tmp_path / "Bad_Thm.tla"
    good.write_text("---- MODULE Good_Thm ----\nTHEOREM TRUE PROOF OBVIOUS\n====\n")
    bad.write_text("---- MODULE Bad_Thm ----\nTHEOREM TRUE PROOF OBVIOUS\n====\n")
    return good, bad


def _flag_bad(monkeypatch, bad):
    # Stand in for the real tlapm scan: report Bad as degenerate, Good as clean.
    monkeypatch.setattr(
        triviality_audit, "audit_dir", lambda directory, **kw: (2, [(str(bad), "placeholder verifies")])
    )


def test_drop_deletes_flagged_task_keeps_rest(tmp_path, monkeypatch):
    good, bad = _make_tasks(tmp_path)
    _flag_bad(monkeypatch, bad)
    flagged = triviality_audit.gate(str(tmp_path), drop=True)
    assert [p for p, _ in flagged] == [str(bad)]
    assert not bad.exists()  # the degenerate task is gone — regeneration self-heals
    assert good.exists()  # a non-degenerate task is untouched


def test_audit_only_keeps_the_file(tmp_path, monkeypatch):
    good, bad = _make_tasks(tmp_path)
    _flag_bad(monkeypatch, bad)
    triviality_audit.gate(str(tmp_path), drop=False)
    assert bad.exists()  # audit mode reports but never deletes


def test_manifest_records_drop_and_files(tmp_path, monkeypatch):
    _good, bad = _make_tasks(tmp_path)
    _flag_bad(monkeypatch, bad)
    manifest = tmp_path / "m.json"
    triviality_audit.gate(str(tmp_path), manifest_path=str(manifest), drop=True)
    data = json.loads(manifest.read_text())
    assert data["dropped"] is True
    assert data["flagged"] == 1
    assert data["failures"][0]["file"] == "Bad_Thm.tla"


def test_no_degenerate_tasks_is_noop(tmp_path, monkeypatch):
    good, _bad = _make_tasks(tmp_path)
    monkeypatch.setattr(triviality_audit, "audit_dir", lambda directory, **kw: (2, []))
    assert triviality_audit.gate(str(tmp_path), drop=True) == []
    assert good.exists()
