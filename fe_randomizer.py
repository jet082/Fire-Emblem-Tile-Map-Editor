
import os
import sys
import json
import random
import hashlib
import struct
import re
from PIL import Image
import argparse
try:
    import google.generativeai as genai
except ImportError:
    genai = None

# --- Constants ---
TILE_SIZE = 16
TILE_REFERENCES_PATH = "tiles/tileReferences.json"
TILE_IMAGES_BASE_PATH = "tiles/images"
MAP_JSON_BASE_PATH = "References/Fire Emblem Map JSON Files"

TILE_CODE_MAP = {
    'PLAIN': 'P', 'PLAIN-FLAT': 'P', 'PLAIN-PLAIN': 'P', 'PLAIN-ROAD': 'p', 'PLAIN-SAND': 'P',
    'MOUNTAIN': 'M', 'MOUNTAIN-PEAK': 'M', 'PEAK': 'K', 'PEAK-PLAIN': 'M',
    'FOREST': 'F', 'WOODS': 'F', 'THICKET': 'F',
    'LAKE': 'L', 'LAKE-CLIFF': 'L', 'RIVER': 'R', 'SEA': 'S', 'WATER': 'W', 'DEEPS': 'S',
    'DESERT': 'D', 'SAND': 'D',
    'CLIFF': 'X', 'CLIFF-GLACIER': 'X', 'CLIFF-VALLEY': 'X', 'VALLEY': 'v',
    'WALL': '#', 'WALL-BRACE': '#', 'WALL-DOOR': '#', 'WALL-FENCE': '#', 'WALL-FLOOR': '#', 'WALL-PILLAR': '#', 'WALL-ROOF': '#', 'WALL2': '#', 'BRACE-WALL': '#', 'DASHDASH-WALL': '#',
    'FLOOR': '.', 'FLOOR-FLAT': '.', 'FLOOR-STAIRS': '.', 'FLOOR-WALL': '.', 'ROAD-FLOOR': '.',
    'GATE': 'G', 'THRONE': 'T', 'CHEST': '?', 'DOOR': 'd', 'STAIRS': 'A',
    'HOUSE': 'H', 'VILLAGE': 'V', 'VILLAGE-HOUSE': 'V', 'VILLAGE-RUINS': 'V', 'RUINS': 'U',
    'FORT': 'f', 'ARENA': '@', 'ARMORY': 'm', 'VENDOR': 'n', 'SHOP-ARMORY': 'm', 'SHOP-VENDOR': 'n', 'INN': 'i',
    'BRIDGE': 'B', 'ROAD': 'r', 'SNAG': 's',
    'DECK': 'E', 'GUNNEL': 'e', 'GUNNELS': 'e', 'MAST': '|',
    'SKY': '^', 'DASHDASH-SKY': '^',
    'BONE': 'b', 'DASHDASH-BONE': 'b',
    'GLACIER': 'z', 'DASHDASH-GLACIER': 'z',
    'FLAT': '_',
    'DASHDASH': ' ', 'EMPTY': ' '
}

CODE_TO_GROUP = {v: k for k, v in TILE_CODE_MAP.items() if k in ['PLAIN', 'MOUNTAIN', 'FOREST', 'LAKE', 'RIVER', 'WALL', 'FLOOR', 'THRONE', 'GATE', 'VILLAGE', 'ROAD', 'SEA', 'DESERT']}

GAME_CONFIGS = {
    "BE8E": {
        "name": "Fire Emblem 8 (U)",
        "map_table": 0x8B0890,
        "event_ptr_table": 0x8B363C,
        "entry_size": 148,
        "num_missions": 77,
        "map_plist_offset": 8,
        "unit_ptr_offset": 0x70,
        "char_table": 0x8B3D30,
        "char_entry_size": 52,
        "main_char_id": 1,
        "text_table": 0x15D48C,
        "json_dir": "Fire Emblem 8/Chapters"
    },
    "AE7E": {
        "name": "Fire Emblem 7 (U)",
        "map_table": 0xC941D0,
        "event_ptr_table": 0xC999C0,
        "entry_size": 84,
        "num_missions": 100,
        "map_plist_offset": 4,
        "unit_ptr_offset": 0x2C,
        "char_table": 0xBDCEE0,
        "char_entry_size": 52,
        "main_char_id": 1,
        "text_table": 0xB808AC,
        "json_dir": "Fire Emblem 7/Chapters"
    },
    "AFEJ": {
        "name": "Fire Emblem 6 (J)",
        "map_table": 0x664410,
        "event_ptr_table": 0x667798,
        "entry_size": 52,
        "num_missions": 50,
        "map_plist_offset": 0, # Direct pointer to plist-like table
        "unit_ptr_offset": 0x20,
        "char_table": 0x6076A0,
        "char_entry_size": 48,
        "main_char_id": 1,
        "text_table": 0x144514,
        "json_dir": "Fire Emblem 6/Chapters"
    }
}

# --- LZ77 Compression ---
class LZ77:
    @staticmethod
    def decompress(data, offset):
        if data[offset] != 0x10:
            return None
        size = struct.unpack("<I", data[offset:offset+4])[0] >> 8
        offset += 4
        out = bytearray()
        while len(out) < size:
            flags = data[offset]
            offset += 1
            for i in range(7, -1, -1):
                if len(out) >= size:
                    break
                if (flags >> i) & 1:
                    block = struct.unpack(">H", data[offset:offset+2])[0]
                    offset += 2
                    length = (block >> 12) + 3
                    disp = (block & 0xFFF) + 1
                    for _ in range(length):
                        out.append(out[-disp])
                else:
                    out.append(data[offset])
                    offset += 1
        return out

    @staticmethod
    def compress(data):
        out = bytearray([0x10])
        size = len(data)
        out.extend(struct.pack("<I", size)[0:3])

        pos = 0
        while pos < size:
            flags = 0
            block = bytearray()
            for i in range(8):
                if pos >= size:
                    break

                # Simple greedy match
                match_len = 0
                match_disp = 0
                max_len = min(size - pos, 18)
                for disp in range(1, min(pos, 4096) + 1):
                    l = 0
                    while l < max_len and data[pos + l] == data[pos - disp + l]:
                        l += 1
                    if l >= 3 and l > match_len:
                        match_len = l
                        match_disp = disp

                if match_len >= 3:
                    flags |= (1 << (7 - i))
                    val = ((match_len - 3) << 12) | (match_disp - 1)
                    block.extend(struct.pack(">H", val))
                    pos += match_len
                else:
                    block.append(data[pos])
                    pos += 1
            out.append(flags)
            out.extend(block)
        return out

# --- AI Engine ---
class GeminiEngine:
    def __init__(self, api_key=None, use_mock=False):
        self.use_mock = use_mock
        if not use_mock and api_key and genai:
            genai.configure(api_key=api_key)
            self.model = genai.GenerativeModel('gemini-1.5-flash')
        else:
            self.model = None

    def generate_mission_pack(self, chapter_num):
        if self.use_mock or not self.model:
            return self._mock_mission_pack(chapter_num)

        prompt = f"""
        Generate a Fire Emblem mission design for Chapter {chapter_num}.
        Return a JSON object with:
        - "title": Mission title.
        - "plot": 2-3 sentence plot summary.
        - "dialogue": 5 lines of dialogue script.
        - "main_char": {{"name": str, "class": str, "bio": str}}
        - "macro_grid": A 10x8 grid of single characters representing terrain:
          P=Plain, M=Mountain, F=Forest, L=Lake, R=River, #=Wall, .=Floor, G=Gate, T=Throne, V=Village, r=Road.
          Make the grid sensible (e.g. Throne inside Walls, Roads connecting Villages).
        """
        try:
            response = self.model.generate_content(prompt)
            # Basic JSON extraction
            text = response.text
            match = re.search(r'{{.*}}', text, re.DOTALL)
            if match:
                return json.loads(match.group(0))
        except Exception as e:
            print(f"AI Generation failed: {e}")

        return self._mock_mission_pack(chapter_num)

    def _mock_mission_pack(self, chapter_num):
        return {
            "title": f"The Road to {chapter_num}",
            "plot": f"The heroes must cross the border to reach chapter {chapter_num}.",
            "dialogue": "Let's move out!\nEnemy sighted!\nWe must defend the village.",
            "main_char": {"name": "Hero", "class": "Lord", "bio": "A brave soul."},
            "macro_grid": [
                "PPPPPPPPPP",
                "PFFFFFPPPP",
                "PF...FPPPP",
                "PF.T.FPPPP",
                "PF...FPPPP",
                "PFFFFFPPPP",
                "PPPPPPPPPP",
                "rrrrrrrrrr"
            ]
        }

# --- Map Generation ---
class MapGenerator:
    def __init__(self, tile_refs):
        self.tile_refs = tile_refs
        self.hash_to_ref = {r['tileHash']: r for r in tile_refs}
        self.groups = {}
        for r in tile_refs:
            g = r['group']
            if g not in self.groups:
                self.groups[g] = []
            self.groups[g].append(r['tileHash'])

    def generate(self, width, height, macro_grid_data=None):
        # WFC-ish algorithm
        grid = [[set(self.hash_to_ref.keys()) for _ in range(width)] for _ in range(height)]

        if macro_grid_data:
            # macro_grid_data is a list of strings
            mg_h = len(macro_grid_data)
            mg_w = len(macro_grid_data[0])

            for y in range(height):
                for x in range(width):
                    mg_x = min(x * mg_w // width, mg_w - 1)
                    mg_y = min(y * mg_h // height, mg_h - 1)
                    code = macro_grid_data[mg_y][mg_x]
                    target_group = CODE_TO_GROUP.get(code, "PLAIN")

                    if target_group in self.groups:
                        group_tiles = set(self.groups[target_group])
                        intersection = grid[y][x].intersection(group_tiles)
                        if intersection:
                            grid[y][x] = intersection

        # Collapse cells
        collapsed_map = [[None for _ in range(width)] for _ in range(height)]

        def get_possible_neighbors(tile_hash, direction):
            ref = self.hash_to_ref.get(tile_hash)
            if not ref: return set()
            return set(ref.get(direction.lower(), []))

        while True:
            # Find cell with minimum non-zero entropy
            min_entropy = float('inf')
            best_cell = None

            for y in range(height):
                for x in range(width):
                    if collapsed_map[y][x] is None:
                        entropy = len(grid[y][x])
                        if entropy == 0: # Contradiction
                            entropy = 1e9 # High penalty
                        if entropy < min_entropy:
                            min_entropy = entropy
                            best_cell = (x, y)

            if best_cell is None:
                break

            x, y = best_cell
            if not grid[y][x]:
                # Pick a random PLAIN tile as fallback
                collapsed_map[y][x] = random.choice(self.groups.get("PLAIN", list(self.hash_to_ref.keys())))
            else:
                collapsed_map[y][x] = random.choice(list(grid[y][x]))

            # Propagate constraints
            queue = [(x, y)]
            while queue:
                cx, cy = queue.pop(0)
                for dx, dy, dir_name, opp_dir in [(0, -1, "NORTH", "SOUTH"), (0, 1, "SOUTH", "NORTH"), (-1, 0, "WEST", "EAST"), (1, 0, "EAST", "WEST")]:
                    nx, ny = cx + dx, cy + dy
                    if 0 <= nx < width and 0 <= ny < height and collapsed_map[ny][nx] is None:
                        possible_neighbors = set()
                        # This is still a bit slow, but more accurate
                        # For a truly sensible map, we only care about the collapsed cell's effect on its neighbors
                        allowed = get_possible_neighbors(collapsed_map[cy][cx], dir_name)
                        new_grid = grid[ny][nx].intersection(allowed)
                        if len(new_grid) < len(grid[ny][nx]):
                            grid[ny][nx] = new_grid
                            # In a full WFC we would add (nx, ny) to queue, but here we only propagate from collapsed cells for speed

        return collapsed_map

# --- Character Randomization ---
class CharacterManager:
    def __init__(self, rom_handler):
        self.rom = rom_handler
        # Basic FE8 Classes (approximate)
        self.classes = [0x01, 0x05, 0x09, 0x0D, 0x19, 0x1D, 0x21, 0x25, 0x2D, 0x3D, 0x48]

    def randomize_character(self, char_id, name=None):
        config = self.rom.config
        if 'char_table' not in config: return

        entry_addr = config['char_table'] + (char_id * config['char_entry_size'])
        if entry_addr + config['char_entry_size'] > len(self.rom.data): return

        # Update Name if provided
        if name:
            text_id = 0x100 + char_id
            self.rom.insert_text(text_id, name)
            struct.pack_into("<H", self.rom.data, entry_addr, text_id)

        # Randomize Class
        new_class = random.choice(self.classes)
        self.rom.data[entry_addr + 5] = new_class

        # Randomize Stats (Bases)
        for offset in range(12, 19): # HP, Str, Skl, Spd, Def, Res, Lck
            self.rom.data[entry_addr + offset] = random.randint(0, 10)

        # Randomize Growths
        for offset in range(28, 35):
            self.rom.data[entry_addr + offset] = random.randint(20, 80)

    def randomize_all(self):
        """Randomizes the entire character table once."""
        if 'char_table' not in self.rom.config: return
        print("Randomizing global character pool...")
        for i in range(1, 255): # Max 255 characters
            self.randomize_character(i)

# --- Unit Placement ---
class UnitPlacer:
    def __init__(self, rom_handler):
        self.rom = rom_handler

    def generate_units(self, mission_map, tile_refs, main_char_id=1):
        units = []
        height = len(mission_map)
        width = len(mission_map[0])
        hash_to_group = {r['tileHash']: r['group'] for r in tile_refs}

        # 1. Place Player Units
        # Find some PLAIN or FLOOR tiles for players
        player_spots = []
        for y in range(height):
            for x in range(width):
                if hash_to_group.get(mission_map[y][x]) in ["PLAIN", "FLOOR"]:
                    player_spots.append((x, y))

        random.shuffle(player_spots)

        # Main Character
        if player_spots:
            px, py = player_spots.pop()
            units.append({
                "char": main_char_id, "class": 0x01, "level": 1, "alliance": 0,
                "x": px, "y": py, "items": [0x01, 0, 0, 0], "ai": [0, 0, 0, 0]
            })

        # A few allies
        for i in range(min(5, len(player_spots))):
            px, py = player_spots.pop()
            units.append({
                "char": 2 + i, "class": random.choice([0x05, 0x09, 0x0D]), "level": 1, "alliance": 0,
                "x": px, "y": py, "items": [0x01, 0, 0, 0], "ai": [0, 0, 0, 0]
            })

        # 2. Place enemies
        # Find THRONE or GATE for Boss
        boss_placed = False
        for y in range(height):
            for x in range(width):
                group = hash_to_group.get(mission_map[y][x], "PLAIN")
                if group in ["THRONE", "GATE"] and not boss_placed:
                    units.append({
                        "char": 0x40 + random.randint(0, 10), "class": 0x05, "level": 5, "alliance": 1,
                        "x": x, "y": y, "items": [0x14, 0, 0, 0], "ai": [3, 3, 9, 0x20]
                    })
                    boss_placed = True

        # Add some random mooks
        for _ in range(15):
            rx, ry = random.randint(0, width-1), random.randint(0, height-1)
            # Ensure not on a wall or deep water
            group = hash_to_group.get(mission_map[ry][rx], "PLAIN")
            if group not in ["WALL", "SEA", "DEEPS", "SKY"]:
                units.append({
                    "char": 0x80 + random.randint(0, 50), "class": random.choice([0x01, 0x05, 0x3F]), "level": 1, "alliance": 1,
                    "x": rx, "y": ry, "items": [0x01, 0, 0, 0], "ai": [0, 0, 9, 0]
                })

        return units

# --- Dialogue Generation ---
class DialogueGenerator:
    def __init__(self):
        self.names = ["Eirika", "Ephraim", "Seth", "Joshua", "L'Arachel", "Lyon", "Eliwood", "Hector", "Lyn", "Ninian", "Roy", "Lilina", "Marth", "Sigurd"]
        self.locations = ["Renais", "Frelia", "Grado", "Jehanna", "Rausten", "Pherae", "Ostia", "Caelin"]
        self.enemies = ["Brigands", "Monsters", "Imperial Soldiers", "Black Fang", "Bern's Army"]

        self.templates = [
            "Lord {name}, the {enemy} are approaching {location}!",
            "We must defend the castle of {location} from the {enemy}.",
            "I cannot believe {name} would betray us to the {enemy}!",
            "Take the {enemy} head-on! For the glory of {location}!",
            "Is that you, {name}? I've been searching for you in {location}."
        ]

    def generate_dialogue(self, num_lines=5):
        lines = []
        for _ in range(num_lines):
            t = random.choice(self.templates)
            lines.append(t.format(
                name=random.choice(self.names),
                enemy=random.choice(self.enemies),
                location=random.choice(self.locations)
            ))
        return "\n".join(lines)

# --- ROM Handler ---
class ROMHandler:
    def __init__(self, rom_path):
        with open(rom_path, "rb") as f:
            self.data = bytearray(f.read())
        self.game_id = self.data[0xAC:0xB0].decode('ascii', errors='ignore')
        if self.game_id not in GAME_CONFIGS:
            # Try to find by pattern
            self.game_id = self._autodetect_game()
            if self.game_id not in GAME_CONFIGS:
                raise ValueError(f"Unsupported Game ID: {self.game_id}")

        self.config = GAME_CONFIGS[self.game_id]
        self._verify_tables()
        self.hash_to_index = {} # To be filled by learning

    def _autodetect_game(self):
        # Scan first 0x200 for IDs
        header = self.data[:0x200]
        if b"FIREEMBLEM8" in header or b"BE8E" in header: return "BE8E"
        if b"FIREEMBLEM7" in header or b"AE7E" in header: return "AE7E"
        if b"FIREEMBLEM6" in header or b"AFEJ" in header: return "AFEJ"
        return "UNKNOWN"

    def _verify_tables(self):
        # Basic check if map_table pointer at 0 looks like a ROM pointer
        tbl = self.config['map_table']
        if tbl < len(self.data):
            ptr = struct.unpack_from("<I", self.data, tbl)[0]
            if not (0x08000000 <= ptr <= 0x09FFFFFF):
                print(f"Warning: map_table at {hex(tbl)} doesn't look like a pointer table (Value: {hex(ptr)})")

    def learn_mappings(self):
        """
        Learns mapping between tile hashes and ROM indices by comparing
        original ROM map data with extracted JSON maps.
        """
        json_base = os.path.join(MAP_JSON_BASE_PATH, self.config['json_dir'])
        if not os.path.exists(json_base):
            print(f"Warning: Map JSON base path '{json_base}' not found. Using dummy mapping.")
            return

        print(f"Learning mappings for {self.config['name']}...")
        # Scan some chapters to build mapping
        for map_id in range(10): # Check first 10 chapters
            entry_addr = self.get_chapter_entry(map_id)
            if entry_addr + self.config['entry_size'] > len(self.data):
                continue

            # Use plist logic
            plist_idx = self.data[entry_addr + self.config['map_plist_offset']]
            if plist_idx == 0: continue
            ptr_addr = self.config['event_ptr_table'] + plist_idx * 4

            if not ptr_addr or ptr_addr >= len(self.data): continue

            map_ptr = struct.unpack("<I", self.data[ptr_addr:ptr_addr+4])[0] & 0xFFFFFF
            if map_ptr == 0 or map_ptr >= len(self.data): continue

            try:
                rom_map_data = LZ77.decompress(self.data, map_ptr)
                if not rom_map_data: continue

                # Find matching JSON file
                # Chapter 1 is usually Map ID 1 or 2
                json_path = os.path.join(json_base, f"{map_id:02d}/001.png.json")
                if not os.path.exists(json_path): continue

                with open(json_path, "r") as f:
                    json_map = json.load(f)

                # Match tiles
                rows = len(json_map)
                cols = len(json_map[0])
                for y in range(rows):
                    for x in range(cols):
                        idx = y * cols + x
                        if idx * 2 + 1 < len(rom_map_data):
                            tile_idx = struct.unpack("<H", rom_map_data[idx*2:idx*2+2])[0]
                            tile_hash = json_map[y][x]
                            self.hash_to_index[tile_hash] = tile_idx
            except Exception as e:
                print(f"Failed to learn from map {map_id}: {e}")

        print(f"Learned {len(self.hash_to_index)} tile mappings.")

    def get_chapter_entry(self, map_id):
        return self.config['map_table'] + map_id * self.config['entry_size']

    def insert_map(self, map_id, map_indices):
        # Convert list of indices to bytes
        raw_map = bytearray()
        for idx in map_indices:
            raw_map.extend(struct.pack("<H", idx))

        compressed = LZ77.compress(raw_map)

        # Append to ROM
        new_addr = len(self.data)
        while len(self.data) % 4 != 0:
            self.data.append(0)
        new_addr = len(self.data)
        self.data.extend(compressed)

        entry_addr = self.get_chapter_entry(map_id)
        if entry_addr + self.config['entry_size'] > len(self.data):
            return False

        if self.game_id == "AFEJ": # FE6 direct pointer logic
            table_ptr = struct.unpack_from("<I", self.data, entry_addr)[0] & 0xFFFFFF
            if table_ptr == 0 or table_ptr >= len(self.data): return False
            struct.pack_into("<I", self.data, table_ptr, new_addr | 0x08000000)
        else: # FE7/FE8 Plist logic
            plist_idx = self.data[entry_addr + self.config['map_plist_offset']]
            if plist_idx == 0:
                print(f"Skipping map {map_id}: Plist index is 0")
                return False
            ptr_addr = self.config['event_ptr_table'] + plist_idx * 4
            if ptr_addr + 4 > len(self.data): return False
            struct.pack_into("<I", self.data, ptr_addr, new_addr | 0x08000000)

        print(f"Inserted map {map_id} at {hex(new_addr)}")
        return True

    def insert_text(self, text_id, text):
        """
        Inserts plain text into the ROM and updates the text table.
        Note: This ignores Huffman compression for simplicity.
        """
        # Convert text to FE character encoding (basic ASCII for now)
        encoded = bytearray()
        for char in text:
            encoded.append(ord(char))
        encoded.append(0) # Null terminator

        # Append to ROM
        new_addr = len(self.data)
        while len(self.data) % 4 != 0:
            self.data.append(0)
        new_addr = len(self.data)
        self.data.extend(encoded)

        # Update pointer in text table
        table_addr = self.config['text_table']
        ptr_addr = table_addr + text_id * 4
        if ptr_addr + 4 <= len(self.data):
            # We set the high bit to 0 to indicate uncompressed text if possible
            # In FE8, uncompressed text often works if it's not in the Huffman range
            struct.pack_into("<I", self.data, ptr_addr, new_addr | 0x08000000)
            print(f"Inserted dialogue at {hex(new_addr)} for text ID {text_id}")

    def insert_unit_data(self, map_id, units):
        """
        Inserts a block of unit data and returns its address.
        """
        raw = bytearray()
        for u in units:
            entry = bytearray(20)
            entry[0] = u['char']
            entry[1] = u['class']
            entry[2] = 0 # Leader
            entry[3] = (u['level'] << 3) | u['alliance']
            entry[4] = u['x']
            entry[5] = u['y']
            entry[6] = u['x']
            entry[7] = u['y']
            for idx, item in enumerate(u['items']):
                entry[8 + idx] = item
            for idx, val in enumerate(u['ai']):
                entry[12 + idx] = val
            raw.extend(entry)
        raw.extend(bytearray(20)) # Termination entry

        new_addr = len(self.data)
        while len(self.data) % 4 != 0:
            self.data.append(0)
        new_addr = len(self.data)
        self.data.extend(raw)

        # Update Chapter Table unit pointers
        entry_addr = self.get_chapter_entry(map_id)
        if entry_addr + self.config['entry_size'] <= len(self.data):
            # Update multiple slots (Normal/Hard, Player/Enemy)
            for offset in range(0, 16, 4): # Usually 4 pointers
                ptr_addr = entry_addr + self.config['unit_ptr_offset'] + offset
                if ptr_addr + 4 <= len(self.data):
                    struct.pack_into("<I", self.data, ptr_addr, new_addr | 0x08000000)

        print(f"Inserted unit data for mission {map_id} at {hex(new_addr)}")
        return new_addr

    def save(self, output_path):
        with open(output_path, "wb") as f:
            f.write(self.data)

# --- Main Script ---
def main():
    parser = argparse.ArgumentParser(description="Fire Emblem Map & Dialogue Randomizer")
    parser.add_argument("--rom", help="Path to Fire Emblem GBA ROM")
    parser.add_argument("--output", default="randomized", help="Base name for output files")
    parser.add_argument("--missions", type=int, help="Number of missions to generate (default: all)")
    parser.add_argument("--api-key", help="Google API Key for Gemini")
    args = parser.parse_args()

    print("Loading tile references...")
    try:
        with open(TILE_REFERENCES_PATH, "r") as f:
            tile_refs = json.load(f)
    except FileNotFoundError:
        print(f"Error: {TILE_REFERENCES_PATH} not found.")
        sys.exit(1)

    gen = MapGenerator(tile_refs)
    dial = DialogueGenerator()

    rom_handler = None
    char_mgr = None
    unit_placer = None
    if args.rom:
        try:
            rom_handler = ROMHandler(args.rom)
            rom_handler.learn_mappings()
            char_mgr = CharacterManager(rom_handler)
            char_mgr.randomize_all()
            unit_placer = UnitPlacer(rom_handler)
        except Exception as e:
            print(f"Error loading ROM: {e}")
            rom_handler = None

    api_key = os.environ.get("GOOGLE_API_KEY") or args.api_key
    ai = GeminiEngine(api_key=api_key, use_mock=(not api_key))

    num_missions = args.missions
    if num_missions is None:
        if rom_handler:
            num_missions = rom_handler.config['num_missions']
        else:
            num_missions = 3 # Fallback if no ROM

    for i in range(0, num_missions):
        print(f"Generating mission {i}...")
        pack = ai.generate_mission_pack(i)
        print(f"Title: {pack['title']}")

        # 1. Generate Map
        width, height = 30, 20 # Larger default
        mission_map = gen.generate(width, height, macro_grid_data=pack['macro_grid'])

        # 2. Generate Image
        mission_img = Image.new("RGB", (width * TILE_SIZE, height * TILE_SIZE))
        for y in range(height):
            for x in range(width):
                tile_hash = mission_map[y][x]
                group = gen.hash_to_ref[tile_hash]['group']
                tile_path = os.path.join(TILE_IMAGES_BASE_PATH, group, f"{tile_hash}.png")
                if os.path.exists(tile_path):
                    with Image.open(tile_path) as t_img:
                        mission_img.paste(t_img, (x * TILE_SIZE, y * TILE_SIZE))

        mission_img.save(f"{args.output}_mission_{i}_map.png")

        # 3. Generate Dialogue
        dialogue = pack['dialogue']
        with open(f"{args.output}_mission_{i}_dialogue.txt", "w") as f:
            f.write(f"TITLE: {pack['title']}\n")
            f.write(f"PLOT: {pack['plot']}\n")
            f.write(f"MAIN CHARACTER: {pack['main_char']['name']} ({pack['main_char']['class']})\n")
            f.write(f"BIO: {pack['main_char']['bio']}\n")
            f.write("------------------\n")
            f.write(dialogue)

        # 4. Insert into ROM if possible
        if rom_handler:
            # Randomize main character for this mission
            main_char_id = rom_handler.config.get('main_char_id', 1)
            char_mgr.randomize_character(main_char_id, name=pack['main_char']['name'])

            # Use learned indices
            map_indices = []
            for y in range(height):
                for x in range(width):
                    tile_hash = mission_map[y][x]
                    # Default to PLAIN tile if hash not learned
                    idx = rom_handler.hash_to_index.get(tile_hash, 0)
                    map_indices.append(idx)

            rom_handler.insert_map(i, map_indices)
            # Insert dialogue (using text IDs 0x900 + i as a safe-ish range)
            rom_handler.insert_text(0x900 + i, dialogue)

            # 5. Place units
            units = unit_placer.generate_units(mission_map, tile_refs, main_char_id=main_char_id)
            unit_addr = rom_handler.insert_unit_data(i, units)

    if rom_handler:
        rom_handler.save(f"{args.output}.gba")
        print(f"Randomized ROM saved as {args.output}.gba")

if __name__ == "__main__":
    main()
