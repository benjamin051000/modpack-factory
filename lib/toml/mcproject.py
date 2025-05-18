from pathlib import Path
import tomlkit


def init_mcproject_toml(directory: Path, force=False):
    assert directory.is_dir()

    doc = tomlkit.document()
    project = tomlkit.table()
    project.add("name", "my-minecraft-modpack")
    project.add("mods", tomlkit.array())
    doc.add("project", project)

    new_path = directory / "mcproject.toml"

    if not force and new_path.exists():
        raise FileExistsError(new_path)

    with open(new_path, "w") as f:
        tomlkit.dump(doc, f)

    return new_path


def read_mcproject_toml(filename: Path):
    with open(filename) as f:
        pass


def add_dependency(filename: Path):
    try:
        file = read_mcproject_toml(filename)
    except FileNotFoundError:
        init_mcproject_toml(filename)


def remove_dependency():
    pass
