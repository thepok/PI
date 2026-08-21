# Web ChatGPT Pro requests

This directory stores inspectable prompts for the single authenticated web-Pro
research-director channel. Raw run state, conversation metadata, browser data,
and downloads live under `runs/` and are ignored. Supported conclusions are
distilled into `knowledge/pi/` with provenance and independent review; raw Pro
answers are not proof authority.

Operational invariant: at most one `chatgpt-pro` call may be active. If the CLI
reports a login/account-selection, browser-permission, rate-limit, or break
condition, stop and notify Marcel immediately.
