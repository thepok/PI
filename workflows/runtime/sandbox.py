from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Sequence


class SandboxError(RuntimeError):
    pass


def _split_env_names(values: list[str] | tuple[str, ...] | None) -> list[str]:
    names: list[str] = []
    seen: set[str] = set()
    for raw in values or []:
        for part in str(raw or "").split(","):
            name = part.strip()
            if not name or name in seen:
                continue
            names.append(name)
            seen.add(name)
    return names


def _bool_from_network(raw: Any, *, default: bool = True) -> bool:
    if raw is None:
        return default
    if isinstance(raw, bool):
        return raw
    value = str(raw).strip().lower()
    if value in {"1", "true", "yes", "on", "enabled"}:
        return True
    if value in {"0", "false", "no", "off", "none", "disabled"}:
        return False
    raise SandboxError(f"invalid sandbox network value: {raw!r}")


def _positive_int(raw: Any, *, name: str, default: int) -> int:
    if raw is None or str(raw).strip() == "":
        return default
    try:
        value = int(raw)
    except (TypeError, ValueError) as exc:
        raise SandboxError(f"{name} must be an integer") from exc
    if value <= 0:
        raise SandboxError(f"{name} must be positive")
    return value


@dataclass(frozen=True)
class SandboxConfig:
    enabled: bool = False
    engine: str = "podman"
    image: str = "opencodeworkflow-dev:latest"
    network: bool = True
    env_allowlist: tuple[str, ...] = ()
    cpus: int = 4
    memory: str = "8g"
    timeout_s: int = 3600
    inactivity_timeout_s: int | None = None
    exclude_paths: tuple[str, ...] = ()
    workspace_mode: str = "copy_in_patch_out"
    path_mode: str = "mirror_absolute_paths"

    def to_dict(self) -> dict[str, Any]:
        return {
            "enabled": self.enabled,
            "engine": self.engine,
            "image": self.image,
            "network": self.network,
            "env_allowlist": list(self.env_allowlist),
            "limits": {
                "cpus": self.cpus,
                "memory": self.memory,
                "timeout_s": self.timeout_s,
                "inactivity_timeout_s": self.inactivity_timeout_s,
            },
            "exclude_paths": list(self.exclude_paths),
            "workspace_mode": self.workspace_mode,
            "path_mode": self.path_mode,
            "host_mounts": {
                "run_dir": "rw",
                "home": "none",
                "working_dir": "none",
            },
        }


@dataclass(frozen=True)
class SandboxPaths:
    original_working_dir: Path
    run_dir: Path
    root: Path
    hostfs_root: Path
    workspace_host_path: Path
    baseline_git_path: Path
    patches_dir: Path
    exports_host_path: Path
    patch_path: Path
    export_inventory_path: Path
    container_working_dir: Path
    exports_container_path: Path = Path("/run/sandbox/exports")

    def to_dict(self) -> dict[str, Any]:
        return {
            "original_working_dir": str(self.original_working_dir),
            "container_working_dir": str(self.container_working_dir),
            "workspace_host_path": str(self.workspace_host_path),
            "baseline_git_path": str(self.baseline_git_path),
            "root": str(self.root),
            "patch_path": str(self.patch_path),
            "exports": {
                "container_path": str(self.exports_container_path),
                "host_path": str(self.exports_host_path),
                "inventory_path": str(self.export_inventory_path),
            },
        }


@dataclass(frozen=True)
class SandboxRuntime:
    config: SandboxConfig
    paths: SandboxPaths
    passed_env_names: tuple[str, ...] = field(default_factory=tuple)
    env_overrides: dict[str, str] = field(default_factory=dict, repr=False)

    def to_manifest_dict(self) -> dict[str, Any]:
        payload = self.config.to_dict()
        payload.update(self.paths.to_dict())
        payload["passed_env_names"] = list(self.passed_env_names)
        return payload

    def host_path_for_container_workdir(self, container_path: Path) -> Path:
        container_path = Path(container_path).expanduser().resolve()
        original = self.paths.original_working_dir
        try:
            rel = container_path.relative_to(original)
        except ValueError:
            return container_path
        return (self.paths.workspace_host_path / rel).resolve()

    def build_podman_command(
        self,
        inner_cmd: list[str],
        *,
        container_workdir: Path,
        cidfile: Path | None = None,
    ) -> list[str]:
        network = "slirp4netns" if self.config.network else "none"
        cmd = ["podman"]
        cgroup_manager = str(os.environ.get("OPENCODEWORKFLOW_PODMAN_CGROUP_MANAGER") or "cgroupfs").strip()
        if cgroup_manager:
            cmd.extend(["--cgroup-manager", cgroup_manager])
        cmd.extend(
            [
                "run",
            *([] if cidfile is None else ["--cidfile", str(cidfile)]),
            "--rm",
            "--network",
            network,
            "--cpus",
            str(self.config.cpus),
            "--memory",
            self.config.memory,
            "-v",
            f"{self.paths.run_dir}:{self.paths.run_dir}:rw",
            "-v",
            f"{self.paths.run_dir}:/run:rw",
            "-v",
            f"{self.paths.workspace_host_path}:{self.paths.original_working_dir}:rw",
            "--workdir",
            str(container_workdir),
            ]
        )
        for name in self.passed_env_names:
            if name in os.environ or name in self.env_overrides:
                cmd.extend(["--env", name])
        # Opt-in only: model backends need credentials, but the sandbox must not
        # mount host $HOME by default. OpenCode writes its SQLite/WAL state beside
        # auth.json, so mounting the whole host data directory read-only makes
        # every sandboxed run fail during startup. Give the container a writable
        # ephemeral data directory and expose only the credential file read-only.
        if str(os.environ.get("OPENCODEWORKFLOW_SANDBOX_OPENCODE_AUTH") or "").strip() == "1":
            auth_file = Path.home() / ".local" / "share" / "opencode" / "auth.json"
            if auth_file.is_file():
                opencode_data = self.paths.root / "opencode-data"
                opencode_data.mkdir(parents=True, exist_ok=True)
                cmd.extend(["-v", f"{opencode_data}:/root/.local/share/opencode:rw"])
                cmd.extend(["-v", f"{auth_file}:/root/.local/share/opencode/auth.json:ro"])
            config_dir = Path.home() / ".config" / "opencode"
            if config_dir.is_dir():
                cmd.extend(["-v", f"{config_dir}:/root/.config/opencode:ro"])
                # The pod sees only the copied workspace, the run record, and
                # explicitly mounted tools/credentials. OpenCode otherwise
                # treats mirrored absolute paths and /run exports as external
                # and waits for an interactive permission response.
                sandbox_config = (
                    Path(__file__).resolve().parent
                    / "containers"
                    / "opencode-sandbox-config.json"
                )
                if sandbox_config.is_file():
                    cmd.extend(
                        [
                            "-v",
                            f"{sandbox_config}:/root/.config/opencode/opencode.json:ro",
                        ]
                    )
            # OpenCode's provider/model catalogue is refreshed into a cache
            # file independently of the binary.  A fresh container can
            # therefore have the same OpenCode version and credentials as the
            # host yet reject newly released models (for example MiniMax-M3).
            # Share only the catalogue, not the rest of the host cache.
            model_catalog = Path.home() / ".cache" / "opencode" / "models.json"
            if model_catalog.is_file():
                cmd.extend(
                    [
                        "-v",
                        f"{model_catalog}:/root/.cache/opencode/models.json:ro",
                    ]
                )
        # Optional, explicit research-tool exposure. The default sandbox still
        # mounts no host tools.
        tool_dir_raw = str(
            os.environ.get("OPENCODEWORKFLOW_SANDBOX_TOOL_DIR") or ""
        ).strip()
        if tool_dir_raw:
            tool_dir = Path(tool_dir_raw).expanduser().resolve()
            if not tool_dir.is_dir():
                raise SandboxError(f"sandbox tool directory is missing: {tool_dir}")
            cmd.extend(["-v", f"{tool_dir}:/lab-tools:ro"])
            cmd.extend(
                [
                    "--env",
                    "PATH=/lab-tools:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
                ]
            )
        cmd.append(self.config.image)
        cmd.extend(inner_cmd)
        return cmd

    def force_remove_container(self, cidfile: Path) -> dict[str, Any]:
        """Remove the exact sandbox container recorded by Podman after a timeout."""
        try:
            container_id = cidfile.read_text(encoding="utf-8").strip()
        except OSError as exc:
            return {
                "attempted": False,
                "removed": False,
                "container_id": "",
                "error": f"container id file unavailable: {exc}",
            }
        if not container_id:
            return {
                "attempted": False,
                "removed": False,
                "container_id": "",
                "error": "container id file was empty",
            }
        try:
            result = subprocess.run(
                [self.config.engine, "rm", "-f", container_id],
                capture_output=True,
                text=True,
                timeout=30,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return {
                "attempted": True,
                "removed": False,
                "container_id": container_id,
                "error": str(exc),
            }
        # `podman run --rm` can win the race and remove the container first.
        missing = "no such container" in (result.stderr or "").lower()
        return {
            "attempted": True,
            "removed": result.returncode == 0 or missing,
            "container_id": container_id,
            "returncode": int(result.returncode),
            "stdout": result.stdout.strip(),
            "stderr": result.stderr.strip(),
        }

    def subprocess_env(self) -> dict[str, str]:
        env = dict(os.environ)
        env.update(self.env_overrides)
        return env


def normalize_sandbox_config(
    *,
    enabled: bool = False,
    network: Any = None,
    env_allowlist: list[str] | tuple[str, ...] | None = None,
    cpus: Any = None,
    memory: str = "",
    timeout_s: Any = None,
    inactivity_timeout_s: Any = None,
    exclude_paths: Sequence[str] | None = None,
    image: str = "",
) -> SandboxConfig | None:
    if not enabled:
        return None
    mem = str(memory or "8g").strip()
    if not mem:
        raise SandboxError("sandbox memory must not be empty")
    normalized_excludes: list[str] = []
    for raw_path in exclude_paths or ():
        raw_value = str(raw_path).strip().replace("\\", "/")
        value = raw_value.strip("/")
        path = Path(value)
        if (
            not value
            or raw_value.startswith("/")
            or value in {".", ".."}
            or path.is_absolute()
            or any(part in {"", ".", ".."} for part in path.parts)
        ):
            raise SandboxError(
                "sandbox exclude paths must be non-empty relative paths "
                f"without '.' or '..': {raw_path!r}"
            )
        if value not in normalized_excludes:
            normalized_excludes.append(value)
    return SandboxConfig(
        enabled=True,
        image=str(image or os.environ.get("OPENCODEWORKFLOW_SANDBOX_IMAGE") or "opencodeworkflow-dev:latest").strip(),
        network=_bool_from_network(network, default=True),
        env_allowlist=tuple(_split_env_names(list(env_allowlist or []))),
        cpus=_positive_int(cpus, name="sandbox cpus", default=4),
        memory=mem,
        timeout_s=_positive_int(timeout_s, name="sandbox timeout", default=3600),
        inactivity_timeout_s=(
            _positive_int(
                inactivity_timeout_s,
                name="sandbox inactivity timeout",
                default=900,
            )
            if inactivity_timeout_s is not None
            and str(inactivity_timeout_s).strip() != ""
            else None
        ),
        exclude_paths=tuple(normalized_excludes),
    )


def sandbox_config_from_inputs(inputs: dict[str, Any]) -> SandboxConfig | None:
    enabled = bool(inputs.get("sandbox"))
    raw_limits = inputs.get("sandbox_limits")
    limits = raw_limits if isinstance(raw_limits, dict) else {}
    raw_env = inputs.get("sandbox_env")
    env_values = raw_env if isinstance(raw_env, list) else [str(raw_env)] if raw_env else []
    raw_excludes = inputs.get("sandbox_exclude")
    excludes = (
        [str(item) for item in raw_excludes]
        if isinstance(raw_excludes, list)
        else [str(raw_excludes)]
        if raw_excludes
        else []
    )
    return normalize_sandbox_config(
        enabled=enabled,
        network=inputs.get("sandbox_network"),
        env_allowlist=[str(item) for item in env_values],
        cpus=limits.get("cpus"),
        memory=str(limits.get("memory") or ""),
        timeout_s=limits.get("timeout_s"),
        inactivity_timeout_s=limits.get("inactivity_timeout_s"),
        exclude_paths=excludes,
        image=str(inputs.get("sandbox_image") or ""),
    )


def preflight_sandbox(config: SandboxConfig) -> None:
    if config.engine != "podman":
        raise SandboxError(f"unsupported sandbox engine: {config.engine}")
    if shutil.which("podman") is None:
        raise SandboxError("sandbox requested but podman is not installed or not on PATH")
    version = subprocess.run(["podman", "--version"], capture_output=True, text=True)
    if version.returncode != 0:
        raise SandboxError(f"podman preflight failed: {version.stderr or version.stdout}")
    image = subprocess.run(["podman", "image", "exists", config.image], capture_output=True, text=True)
    if image.returncode != 0:
        raise SandboxError(f"sandbox image is missing: {config.image}")


def _mirrored_path(root: Path, absolute_path: Path) -> Path:
    if not absolute_path.is_absolute():
        raise SandboxError(f"path must be absolute: {absolute_path}")
    return (root / str(absolute_path).lstrip("/")).resolve()


def _copy_tree(
    src: Path,
    dest: Path,
    exclude_paths: Sequence[str] = (),
) -> None:
    if dest.exists():
        shutil.rmtree(dest)
    dest.parent.mkdir(parents=True, exist_ok=True)
    rsync = shutil.which("rsync")
    if rsync:
        command = [
                rsync,
                "-a",
                "--checksum",
                "--delete",
                "--max-size=100m",
                "--exclude",
                ".git/",
                "--exclude",
                ".opencodeworkflow/",
                "--exclude",
                ".workflow_step_support/",
                "--exclude",
                "secrets/",
                "--exclude",
                ".venv/",
                "--exclude",
                ".lake/",
                "--exclude",
                "elan/",
                "--exclude",
                "xdg-cache/",
                "--exclude",
                "litsweep-runs/",
                "--exclude",
                "attacks/617-claude/dualenc/",
                "--exclude",
                "attacks/617-claude/rigidity/certify/.runs/",
        ]
        for relative_path in exclude_paths:
            command.extend(["--exclude", f"/{relative_path}/"])
        command.extend([f"{src}/", f"{dest}/"])
        subprocess.run(command, check=True)
        return

    def ignore_large_generated(directory: str, names: list[str]) -> set[str]:
        ignored = set(
            shutil.ignore_patterns(
                ".git",
                ".opencodeworkflow",
                ".workflow_step_support",
                "secrets",
                ".venv",
                ".lake",
                "elan",
                "xdg-cache",
                "litsweep-runs",
                "dualenc",
                ".runs",
            )(directory, names)
        )
        for name in names:
            path = Path(directory) / name
            relative = path.relative_to(src).as_posix()
            if any(
                relative == excluded
                or relative.startswith(f"{excluded}/")
                for excluded in exclude_paths
            ):
                ignored.add(name)
                continue
            try:
                if path.is_file() and path.stat().st_size > 100 * 1024 * 1024:
                    ignored.add(name)
            except OSError:
                continue
        return ignored

    shutil.copytree(
        src,
        dest,
        ignore=ignore_large_generated,
    )


def prepare_sandbox_workspace(*, config: SandboxConfig, working_dir: Path, run_dir: Path) -> SandboxRuntime:
    preflight_sandbox(config)
    original = working_dir.resolve()
    run_dir = run_dir.resolve()
    root = (run_dir / "sandbox").resolve()
    hostfs_root = (root / "hostfs").resolve()
    workspace = _mirrored_path(hostfs_root, original)
    baseline_git = (root / "patch_git").resolve()
    patches_dir = (root / "patches").resolve()
    exports = (root / "exports").resolve()
    patches_dir.mkdir(parents=True, exist_ok=True)
    exports.mkdir(parents=True, exist_ok=True)
    _copy_tree(original, workspace, config.exclude_paths)
    passed_names: list[str] = []
    seen_names: set[str] = set()
    for name in config.env_allowlist:
        if name in seen_names:
            continue
        if name in os.environ:
            passed_names.append(name)
            seen_names.add(name)

    runtime = SandboxRuntime(
        config=config,
        paths=SandboxPaths(
            original_working_dir=original,
            run_dir=run_dir,
            root=root,
            hostfs_root=hostfs_root,
            workspace_host_path=workspace,
            baseline_git_path=baseline_git,
            patches_dir=patches_dir,
            exports_host_path=exports,
            patch_path=(patches_dir / "working_dir.patch").resolve(),
            export_inventory_path=(exports / "export_inventory.json").resolve(),
            container_working_dir=original,
        ),
        passed_env_names=tuple(passed_names),
        env_overrides={},
    )
    _initialize_patch_baseline(runtime)
    return runtime


def _file_sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _patch_git_command(runtime: SandboxRuntime, *args: str) -> list[str]:
    """Build a Git command for the private baseline index outside the pod tree."""
    return [
        "git",
        f"--git-dir={runtime.paths.baseline_git_path}",
        f"--work-tree={runtime.paths.workspace_host_path}",
        *args,
    ]


# Upper bound for a single baseline/patch git subprocess. Prevents an unbounded
# git hang from silently freezing sandbox setup or finalization (T8 incident
# hardening); generous because `git add -A` over a large research workspace can
# legitimately take minutes.
_PATCH_GIT_TIMEOUT_S = 600


def _run_patch_git(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[Any]:
    try:
        return subprocess.run(command, timeout=_PATCH_GIT_TIMEOUT_S, **kwargs)
    except subprocess.TimeoutExpired as exc:
        raise SandboxError(
            f"sandbox git operation timed out after {_PATCH_GIT_TIMEOUT_S}s: {' '.join(command[:4])} ..."
        ) from exc


_PATCH_TRANSIENT_PATHS = (
    ":(glob,exclude)**/.git/**",
    ":(glob,exclude)**/.opencodeworkflow/**",
    ":(glob,exclude)**/.workflow_step_support/**",
    ":(glob,exclude)**/secrets/**",
    ":(glob,exclude)**/.venv/**",
    ":(glob,exclude)**/.lake/**",
    ":(glob,exclude)**/elan/**",
    ":(glob,exclude)**/xdg-cache/**",
    ":(glob,exclude)**/litsweep-runs/**",
    ":(glob,exclude)attacks/617-claude/dualenc/**",
    ":(glob,exclude)attacks/617-claude/rigidity/certify/.runs/**",
)


def _stage_patch_workspace(runtime: SandboxRuntime) -> None:
    """Stage user artifacts while excluding workflow state and rebuildable caches."""
    pathspecs = [".", *_PATCH_TRANSIENT_PATHS]
    _run_patch_git(
        _patch_git_command(runtime, "add", "-A", "--", *pathspecs),
        check=True,
    )


def _initialize_patch_baseline(runtime: SandboxRuntime) -> None:
    """Snapshot the copied workspace once without making another source tree.

    The former implementation copied the baseline twice more during finalization
    and then staged the third copy. Large research repositories consequently
    needed roughly three complete transient trees. A private Git object/index
    store records the same point-in-time baseline while the pod still sees only
    the ordinary copied workspace and no ``.git`` directory.
    """
    git_dir = runtime.paths.baseline_git_path
    if git_dir.exists():
        shutil.rmtree(git_dir)
    _run_patch_git(["git", "init", "--bare", "--quiet", str(git_dir)], check=True)
    _stage_patch_workspace(runtime)
    _run_patch_git(
        _patch_git_command(
            runtime,
            "-c",
            "user.email=opencodeworkflow@example.invalid",
            "-c",
            "user.name=opencodeworkflow",
            "commit",
            "--quiet",
            "--allow-empty",
            "-m",
            "sandbox baseline",
        ),
        check=True,
    )


def write_export_inventory(runtime: SandboxRuntime) -> list[dict[str, Any]]:
    exports = runtime.paths.exports_host_path
    rows: list[dict[str, Any]] = []
    if exports.exists():
        for path in sorted(p for p in exports.rglob("*") if p.is_file()):
            rows.append(
                {
                    "path": path.relative_to(exports).as_posix(),
                    "size": path.stat().st_size,
                    "sha256": _file_sha256(path),
                }
            )
    payload = {"exports": rows}
    runtime.paths.export_inventory_path.parent.mkdir(parents=True, exist_ok=True)
    runtime.paths.export_inventory_path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    return rows


def export_workspace_patch(runtime: SandboxRuntime) -> dict[str, Any]:
    patch_path = runtime.paths.patch_path
    patch_path.parent.mkdir(parents=True, exist_ok=True)
    git_dir = runtime.paths.baseline_git_path
    if not git_dir.is_dir():
        raise SandboxError("sandbox patch baseline is missing")
    _stage_patch_workspace(runtime)
    diff = _run_patch_git(
        _patch_git_command(runtime, "diff", "--binary", "--cached", "HEAD", "--"),
        capture_output=True,
        text=True,
        check=False,
    )
    patch_path.write_text(diff.stdout or "", encoding="utf-8")
    return {
        "path": str(patch_path),
        "size": patch_path.stat().st_size,
        "sha256": _file_sha256(patch_path),
        "empty": patch_path.stat().st_size == 0,
    }


def finalize_sandbox(runtime: SandboxRuntime) -> dict[str, Any]:
    manifest = runtime.to_manifest_dict()
    try:
        patch = export_workspace_patch(runtime)
        exports = write_export_inventory(runtime)
        return {
            "sandbox": manifest,
            "patch": patch,
            "exports": {
                "container_path": str(runtime.paths.exports_container_path),
                "host_path": str(runtime.paths.exports_host_path),
                "inventory_path": str(runtime.paths.export_inventory_path),
                "files": exports,
            },
        }
    finally:
        # The patch, export inventory, workflow artifacts, and OpenCode session
        # are the durable record. Source/baseline mirrors are multi-gigabyte
        # transient implementation details and make retries exhaust the host.
        for bulk in (
            runtime.paths.hostfs_root,
            runtime.paths.baseline_git_path,
        ):
            if bulk.exists():
                shutil.rmtree(bulk)
