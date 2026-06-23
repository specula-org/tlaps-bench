"""Tests for LiteLLM backend."""

import json
import os
import sys
import tempfile
from unittest.mock import patch

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "src"))

from evaluator.backends.litellm import LiteLLMBackend
from evaluator.backends.litellm_agent import extract_proof


class TestLiteLLMBackend:
    def test_build_command(self):
        backend = LiteLLMBackend(model="gpt-5.5")
        cmd = backend.build_command("/workspace", "/results")
        assert cmd == [
            "python3", "-m", "evaluator.backends.litellm_agent",
            "--workspace", "/workspace",
            "--model", "gpt-5.5",
        ]

    def test_firewall_hosts_openai(self):
        backend = LiteLLMBackend(model="gpt-5.5")
        assert backend.firewall_hosts() == ["api.openai.com"]

    def test_firewall_hosts_anthropic(self):
        backend = LiteLLMBackend(model="anthropic/claude-sonnet-4")
        assert backend.firewall_hosts() == ["api.anthropic.com"]

    def test_firewall_hosts_google(self):
        backend = LiteLLMBackend(model="gemini/gemini-2.5-pro")
        assert backend.firewall_hosts() == ["generativelanguage.googleapis.com"]

    def test_firewall_hosts_deepseek(self):
        backend = LiteLLMBackend(model="deepseek/deepseek-r1")
        assert backend.firewall_hosts() == ["api.deepseek.com"]

    def test_check_auth_openai(self):
        backend = LiteLLMBackend(model="gpt-5.5")
        with patch.dict(os.environ, {"OPENAI_API_KEY": "sk-test"}):
            assert backend.check_auth() is None
        with patch.dict(os.environ, {}, clear=True):
            assert backend.check_auth() is not None

    def test_check_auth_anthropic(self):
        backend = LiteLLMBackend(model="anthropic/claude-sonnet-4")
        with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "sk-ant-test"}):
            assert backend.check_auth() is None
        with patch.dict(os.environ, {}, clear=True):
            assert backend.check_auth() is not None

    def test_env_keys(self):
        backend = LiteLLMBackend()
        assert "OPENAI_API_KEY" in backend.env_keys
        assert "ANTHROPIC_API_KEY" in backend.env_keys

    def test_install_script(self):
        backend = LiteLLMBackend()
        assert backend.install_script == "install-litellm.sh"


class TestParseOutput:
    def test_parse_response_and_usage(self):
        backend = LiteLLMBackend()
        with tempfile.NamedTemporaryFile(mode="w", suffix=".jsonl", delete=False) as f:
            f.write(json.dumps({"type": "response", "text": "Here is the proof...", "attempt": 1}) + "\n")
            f.write(json.dumps({"type": "usage", "input_tokens": 1000, "output_tokens": 500}) + "\n")
            path = f.name

        try:
            transcript, in_tok, out_tok = backend.parse_output(path)
            assert "Here is the proof" in transcript
            assert in_tok == 1000
            assert out_tok == 500
        finally:
            os.unlink(path)

    def test_parse_error(self):
        backend = LiteLLMBackend()
        with tempfile.NamedTemporaryFile(mode="w", suffix=".jsonl", delete=False) as f:
            f.write(json.dumps({"type": "error", "message": "API key invalid"}) + "\n")
            path = f.name

        try:
            transcript, _, _ = backend.parse_output(path)
            assert "API key invalid" in transcript
        finally:
            os.unlink(path)

    def test_parse_missing_file(self):
        backend = LiteLLMBackend()
        transcript, in_tok, out_tok = backend.parse_output("/nonexistent/path.jsonl")
        assert transcript == ""
        assert in_tok == 0
        assert out_tok == 0


class TestExtractProof:
    def test_fenced_code_block(self):
        response = """Here's the proof:

```tla
---- MODULE GCD ----
THEOREM GCD3 == TRUE
  PROOF BY DEF GCD
====
```

That should work."""
        result = extract_proof(response, "")
        assert "MODULE GCD" in result
        assert "THEOREM GCD3" in result
        assert "That should work" not in result

    def test_raw_tla_content(self):
        response = """---- MODULE GCD ----
THEOREM GCD3 == TRUE
  PROOF BY DEF GCD
===="""
        result = extract_proof(response, "")
        assert "MODULE GCD" in result
        assert "====" in result

    def test_tla_with_surrounding_prose(self):
        response = """Here's my solution:
---- MODULE GCD ----
THEOREM GCD3 == TRUE
  PROOF BY DEF GCD
====
Hope this helps!"""
        result = extract_proof(response, "")
        assert "MODULE GCD" in result
        assert "Hope this helps" not in result
