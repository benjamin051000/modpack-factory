import requests

API = "https://api.modrinth.com"
SEARCH = API + "/v2/search"


def search(query: str):
    response = requests.get(SEARCH, params={"query": query})
    return response.json()
