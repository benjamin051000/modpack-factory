import aiohttp
import pytest

from lib.mod.mod import Mod
from lib.sources.modrinth import API


@pytest.mark.asyncio
async def test_mod_from_modrinth():
    async with aiohttp.ClientSession(API) as session:
        sodium = await Mod.from_modrinth(session, "sodium")

    assert sodium.slug == "sodium"
