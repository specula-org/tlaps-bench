"""Focused tests for the Cursor backend's network boundary."""

import os
import sys

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "src"))

from evaluator.backends.cursor import CursorBackend


def test_cursor_firewall_uses_exact_default_api_host(monkeypatch):
    monkeypatch.delenv("CURSOR_API_ENDPOINT", raising=False)

    assert CursorBackend().firewall_hosts() == ["api2.cursor.sh"]


@pytest.mark.parametrize(
    ("endpoint", "hostname"),
    [
        ("https://cursor-gateway.example.com", "cursor-gateway.example.com"),
        ("https://CURSOR-GATEWAY.EXAMPLE.COM:443/v1", "cursor-gateway.example.com"),
        ("https://bücher.example/v1", "xn--bcher-kva.example"),
        ("https://cursor-gateway.example.com./v1", "cursor-gateway.example.com"),
    ],
)
def test_cursor_firewall_uses_configured_https_endpoint(monkeypatch, endpoint, hostname):
    monkeypatch.setenv("CURSOR_API_ENDPOINT", endpoint)

    assert CursorBackend().firewall_hosts() == [hostname]


@pytest.mark.parametrize(
    "endpoint",
    [
        "",
        "api2.cursor.sh",
        "http://api2.cursor.sh",
        "https:///missing-host",
        "https://api2.cursor.sh:8443",
        "https://api2.cursor.sh:not-a-port",
        "https://user@example.com",
        "https://bad_host.example.com",
        "https://127.0.0.1",
        "https://[::1]",
    ],
)
def test_cursor_firewall_rejects_endpoint_it_cannot_enforce(monkeypatch, endpoint):
    monkeypatch.setenv("CURSOR_API_ENDPOINT", endpoint)

    with pytest.raises(ValueError, match="CURSOR_API_ENDPOINT"):
        CursorBackend().firewall_hosts()
