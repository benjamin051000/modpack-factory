# Modpack Factory 🏭
This project is a command-line tool to assist in creating minecraft modpacks.

Its primary purpose is to automatically find a working configuration of the mods you request 
by working out compatible versions of each mod, mod loader, and Minecraft itself.

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
- [ ] import an already-made mcproject.toml
- [ ] incremental SAT solving (when you add a mod to an already-made mcproject.toml)
- [ ] Give multiple solutions to choose from
- [ ] Assist with upgrading mods
