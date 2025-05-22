import aiohttp
import pytest

from lib.sources.modrinth import API

from .mod import Mod


@pytest.mark.asyncio
async def test_mod_from_modrinth():
    async with aiohttp.ClientSession(API) as session:
        sodium = await Mod.from_modrinth(session, "sodium")

    assert sodium.slug == "sodium"
    assert sodium.title == "Sodium"
