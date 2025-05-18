import requests

API = "https://api.modrinth.com/v2"

def search(query: str) -> dict:
    response = requests.get(f"{API}/search", params={"query": query})
    return response.json()


def get_project(slug: str) -> dict:
    return requests.get(f"{API}/project/{slug}").json()


def get_projects(slugs: list[str]) -> dict:
    formatted_slugs = str(slugs).replace("'", '"')  # API requires double-quotes
    return requests.get(f"{API}/projects", params={"ids": formatted_slugs}).json()

def get_versions(slug: str) -> dict:
    return requests.get(f"{API}/project/{slug}/version").json()
