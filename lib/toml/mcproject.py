from pathlib import Path

import tomlkit


def init_mcproject_toml(path: Path, force=False):
    if not force and path.exists():
        raise FileExistsError(path)

    doc = tomlkit.document()
    project = tomlkit.table()
    project.add("name", "my-minecraft-modpack")
    project.add("minecraft-version", ">=1.20.1")  # TODO fetch this default somehow...
    project.add("mods", tomlkit.array())
    doc.add("project", project)

    with open(path, "w") as f:
        tomlkit.dump(doc, f)

    return path


# TODO probably map this to a dataclass too
def read_mcproject_toml(filename: Path) -> tomlkit.TOMLDocument:
    with open(filename) as f:
        return tomlkit.load(f)


def write_mcproject_toml(toml: tomlkit.TOMLDocument, filename: Path):
    toml["project"]["mods"].multiline(True)  # pyright: ignore
    with open(filename, "w") as f:
        tomlkit.dump(toml, f)


def add_mod(toml: tomlkit.TOMLDocument, mod: str) -> bool:
    mods = set(toml["project"]["mods"])  # pyright: ignore
    if mod in mods:
        return False
    toml["project"]["mods"].append(mod)  # pyright: ignore
    return True
