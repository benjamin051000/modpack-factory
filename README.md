# Modpack Factory 🏭

> [!NOTE]
> This tool is currently in a pre-alpha state. Here be dragons! 🐉

This project is a command-line tool to assist in creating minecraft modpacks.

Its primary purpose is to automatically find a working configuration of the mods you request 
by working out compatible versions of each mod, mod loader, and Minecraft itself.

Under the hood, this tool uses a SAT solver to determine what you need to build your modpack.

The design of Modpack Factory is inspired by cargo, pyproject.toml, and uv.

## Features
- Creates mcproject.toml, which tracks your modpack's mods
- Uses SAT solving to determine versions of Minecraft, loader, and mods, given a list of mods

## Usage

### 1. Discover mods

Use the `search` command to find mods by name:

```
❯ uv run main.py search sodium
Results:
Sodium (sodium)
Sodium Extra (sodium-extra)
Sodium Shadowy Path Blocks (sodium-shadowy-path-blocks)
Sodium Dynamic Lights (sodium-dynamic-lights)
Sodium Options API (sodium-options-api)
Sodium Extras (sodium-extras)
Sodium Options Mod Compat (sodium-options-mod-compat)
Sodium Leaf Culling (sodiumleafculling)
Sodium Plus (sodiumplus)
Sodium/Rubidium Occlusion Culling Fix (occlusion-culling-fix-sodium)
```

<!-- Get more information about them with the `info` command: -->
<!-- ``` -->
<!-- uv run main.py info sodium -->
<!-- ``` -->
<!--TODO this command sucks right now, fix it before commenting back in-->

### 2. Add mods to your project

```
❯ uv run main.py add sodium
Added Sodium (sodium)
Selected minecraft version: 1.21.5
Selected mod loader: neoforge
Mods:
- sodium (mc1.21.5-0.6.11-neoforge)
```

Notice that two new files have been created, `mcproject.toml` and `mcproject.lock.toml`:

```toml
# mcproject.toml
[project]
name = "my-minecraft-modpack"
minecraft-version = ">=1.20.1"
mods = [
    "sodium",
]
```

```toml
# mcproject.lock.toml
[[mod]]
slug = "sodium"
version_number = "mc1.21.5-0.6.11-neoforge"
url = "https://cdn.modrinth.com/data/AANobbMI/versions/jv9JbDp8/sodium-neoforge-0.6.11%2Bmc1.21.5.jar"
```
These files keep track of the mods you intend on including in your modpack.

As you add more mods, the tool will automatically determine the version of minecraft, mod loader, and version of each added mod required to play.

## Examples

See [examples/](https://github.com/benjamin051000/modpack-factory/tree/main/examples) for example projects and usage.

## To Do
- [x] first implementation
- [x] lockfile
- [x] lock an already-made mcproject.toml
- [x] add a new mod to an existing mcproject.toml
- [x] specify minecraft version constraints in mcproject.toml
- [ ] specify mod constraints in mcproject.toml
- [ ] specify loader constraints in mcproject.toml
- [ ] group sources (e.g., fabulously optimized) to update independently from additional mods
- [ ] optional dependencies (in fabric.mod.json, for example)
- [ ] curseforge support
- [ ] resource packs
- [ ] shader packs
- [ ] fabric MANIFEST.MF data for fabric versions?
- [ ] neo/forge mod support
- [ ] Give multiple solutions to choose from
- [ ] Assist with upgrading mods
- [ ] launch minecraft?
- [ ] export to Prism launcher
- [ ] support minecraft classic/alpha/beta/snapshot versions
