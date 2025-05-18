import requests

API = "https://api.modrinth.com/v2/"
SEARCH = API + "search"
PROJECT = API + "project"
PROJECTS = API + "projects"


def search(query: str) -> dict:
    response = requests.get(SEARCH, params={"query": query})
    return response.json()


def get_project(slug: str) -> dict:
    return requests.get(f"{PROJECT}/{slug}").json()


def get_projects(slugs: list[str]) -> dict:
    formatted_slugs = str(slugs).replace("'", '"')  # API requires double-quotes
    return requests.get(PROJECTS, params={"ids": formatted_slugs}).json()
