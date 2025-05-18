# Modpack Factory 🏭
This project is a command-line minecraft modpack creation tool.

Its primary purpose is to help you find a working configuration of the mods you supply 
by determining the proper versions of each mod, minecraft, and even selecting the loader.

Under the hood, this tool uses a SAT solver to determine what you need to build your modpack.

Modpack Factory is inspired by cargo and uv for dependency management.

## Features
- Creates mcproject.toml, which tracks your modpack's mods
- Uses SAT solving to determine versions of Minecraft, loader, and mods, given a list of mods

## To Do
- [ ] first implementation
- [ ] lockfile
- [ ] optional dependencies (in fabric.mod.json, for example)
- [ ] curseforge support
- [ ] resource packs
- [ ] shader packs
- [ ] neo/forge mod support
- [ ] fabric MANIFEST.MF data for fabric versions?
