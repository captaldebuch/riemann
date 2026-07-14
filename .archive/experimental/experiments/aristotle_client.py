"""
Thin wrapper around the official `aristotlelib` SDK for this project.

The API key lives in `aristotle-key.txt` at the repo root and is never printed
or logged — it is read once and handed to `aristotlelib.set_api_key`.

The SDK is fully async (httpx under the hood); this module exposes plain
`asyncio.run`-wrapped sync functions since the rest of this project's tooling
(experiments/*.py) is sync.

Usage (per AGENTS.md's "Aristotle-specific instructions"):
    - Send individual .lean files from Discovery/ or Criteria/.
    - Ask it to "fill the sorry" for one specific theorem at a time.
    - Verify any returned proof with `lake build` before accepting it.
"""

import asyncio
import re
from pathlib import Path

from aristotlelib import set_api_key
from aristotlelib.agent_task import AgentTask
from aristotlelib.project import Project

REPO_ROOT = Path(__file__).resolve().parent.parent
KEY_PATH = REPO_ROOT / "aristotle-key.txt"

_KEY_TOKEN_RE = re.compile(r"[A-Za-z0-9_\-\.]{20,}")

_key_loaded = False


def _extract_key(raw: str) -> str:
    """The key file may contain surrounding notes/comments (e.g. a stray
    typographic dash breaks httpx's ASCII header encoding) — pull out the
    single long token that looks like an actual API key instead of trusting
    the whole file verbatim."""
    candidates = _KEY_TOKEN_RE.findall(raw)
    if not candidates:
        raise ValueError("No API-key-shaped token found in aristotle-key.txt")
    return max(candidates, key=len)


def _ensure_key() -> None:
    global _key_loaded
    if not _key_loaded:
        set_api_key(_extract_key(KEY_PATH.read_text()))
        _key_loaded = True


async def _list_projects_async(limit: int = 10) -> list[Project]:
    _ensure_key()
    projects, _ = await Project.list_projects(limit=limit)
    return projects


def list_projects(limit: int = 10) -> list[Project]:
    """Safe, read-only connectivity check — lists past projects, creates nothing."""
    return asyncio.run(_list_projects_async(limit))


async def _fill_sorry_async(project_dir: str | Path, prompt: str, wait: bool) -> tuple[Project, AgentTask | None]:
    _ensure_key()
    proj = await Project.create_from_directory(prompt=prompt, project_dir=project_dir)
    tasks, _ = await proj.get_tasks(limit=1)
    task = tasks[0] if tasks else None
    if wait and task is not None:
        await task.wait_for_completion()
        await task.refresh()
    return proj, task


def fill_sorry(project_dir: str | Path, prompt: str, wait: bool = True) -> tuple[Project, AgentTask | None]:
    """
    Submit a project directory (e.g. a copy of Discovery/ or Criteria/) with
    instructions to fill a specific `sorry`. Returns (Project, AgentTask);
    if wait=True, blocks (with progress output) until the task resolves.

    NOTE: this creates a real, potentially metered task on Harmonic's servers —
    don't call it in a loop without checking cost/quota first.
    """
    return asyncio.run(_fill_sorry_async(project_dir, prompt, wait))


if __name__ == "__main__":
    for p in list_projects():
        print(p.object_id, p.status)
