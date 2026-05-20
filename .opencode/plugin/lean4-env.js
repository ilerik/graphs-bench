// .opencode/plugin/lean4-env.js
//
// Sets the LEAN4_* environment variables that the lean4-skills SKILL.md and
// scripts expect, and points the lean-lsp MCP server at this project's Lean
// subdirectory (formal/lean/). Resolved at session start from the project
// directory, so the config stays portable across machines.

import { join } from "path"

export default async ({ project, worktree, directory }) => {
  const projectDir = worktree ?? project?.worktree ?? project?.directory ?? directory ?? process.cwd()
  const skillRoot = join(projectDir, ".opencode", "lean4-skills", "plugins", "lean4")
  const scripts = join(skillRoot, "lib", "scripts")
  const refs = join(skillRoot, "skills", "lean4", "references")
  const leanProject = join(projectDir, "formal", "lean")

  return {
    config: async (cfg) => {
      if (cfg?.mcp?.["lean-lsp"]) {
        const server = cfg.mcp["lean-lsp"]
        server.env = server.env ?? {}
        if (!server.env.LEAN_PROJECT_PATH) {
          server.env.LEAN_PROJECT_PATH = leanProject
        }
      }
    },
    "shell.env": async (_input, output) => {
      output.env.LEAN4_PLUGIN_ROOT = skillRoot
      output.env.LEAN4_SCRIPTS = scripts
      output.env.LEAN4_REFS = refs
      if (!output.env.LEAN4_PYTHON_BIN) {
        output.env.LEAN4_PYTHON_BIN = "python3"
      }
    },
  }
}
