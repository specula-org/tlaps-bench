"""tlacheck CLI errors must never be reported as a clean audit."""

from tlacheck import cli


def test_audit_error_exits_three(tmp_path, monkeypatch, capsys):
    def fail(*_args, **_kwargs):
        raise RuntimeError("SANY down")

    monkeypatch.setattr(cli, "audit_one", fail)

    exit_code = cli.main([str(tmp_path), "--target", "Foo"])

    assert exit_code == 3
    assert "ERROR" in capsys.readouterr().out
