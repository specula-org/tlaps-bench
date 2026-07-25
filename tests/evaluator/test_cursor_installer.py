"""Regression tests for the Cursor CLI install script."""

import os
import subprocess
from pathlib import Path

INSTALL_SCRIPT = Path("docker/install-scripts/install-cursor.sh").resolve()


def _run_installer(tmp_path, curl_script):
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    fake_curl = fake_bin / "curl"
    fake_curl.write_text(curl_script)
    fake_curl.chmod(0o755)

    home = tmp_path / "home"
    home.mkdir()
    env = os.environ.copy()
    env.update(
        {
            "HOME": str(home),
            "PATH": f"{fake_bin}:{env['PATH']}",
        }
    )
    return subprocess.run(
        ["bash", str(INSTALL_SCRIPT)],
        capture_output=True,
        text=True,
        env=env,
    )


def test_cursor_installer_propagates_curl_failure(tmp_path):
    result = _run_installer(
        tmp_path,
        """#!/bin/bash
exit 22
""",
    )

    assert result.returncode == 22


def test_cursor_installer_rejects_missing_executable(tmp_path):
    result = _run_installer(
        tmp_path,
        """#!/bin/bash
printf '#!/bin/bash\\nexit 0\\n'
""",
    )

    assert result.returncode != 0
    assert "Cursor installer did not create executable" in result.stderr
