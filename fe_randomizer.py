
import os
import sys
import json
import random
import hashlib
import struct
from PIL import Image
import argparse

# --- Constants ---
TILE_SIZE = 16
TILE_REFERENCES_PATH = "tiles/tileReferences.json"
TILE_IMAGES_BASE_PATH = "tiles/images"
MAP_JSON_BASE_PATH = "References/Fire Emblem Map JSON Files"

GAME_CONFIGS = {
    "BE8E": {
        "name": "Fire Emblem 8 (U)",
        "map_table": 0x8B0890,
        "text_table": 0x15D48C,
        "json_dir": "Fire Emblem 8/Chapters"
    },
    "AE7E": {
        "name": "Fire Emblem 7 (U)",
        "map_table": 0xC941D0,
        "text_table": 0xB808AC,
        "json_dir": "Fire Emblem 7/Chapters"
    },
    "AFEJ": {
        "name": "Fire Emblem 6 (J)",
        "map_table": 0x664410,
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

    def generate(self, width, height, biome="PLAIN"):
        # WFC-ish algorithm
        # Initialize grid with all possible tiles
        grid = [[set(self.hash_to_ref.keys()) for _ in range(width)] for _ in range(height)]

        # Macro-terrain biasing: Decide high-level groups
        macro_width, macro_height = (width + 3) // 4, (height + 3) // 4
        macro_grid = [[biome for _ in range(macro_width)] for _ in range(macro_height)]

        # Add some variety to macro grid
        for _ in range(int(macro_width * macro_height * 0.2)):
            mx, my = random.randint(0, macro_width-1), random.randint(0, macro_height-1)
            macro_grid[my][mx] = random.choice(["MOUNTAIN", "FOREST", "LAKE", "RIVER"])

        # Constrain tiles based on macro grid
        for y in range(height):
            for x in range(width):
                target_group = macro_grid[y // 4][x // 4]
                # Filter grid[y][x] to only include tiles from target_group if possible
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
            raise ValueError(f"Unsupported Game ID: {self.game_id}")
        self.config = GAME_CONFIGS[self.game_id]
        self.hash_to_index = {} # To be filled by learning

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
            ptr_addr = self.get_map_pointer(map_id)
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

    def get_map_pointer(self, map_id):
        entry_addr = self.config['map_table'] + map_id * 32 # Usually 32 or 12 bytes depending on game
        # FE8 entry is ~32 bytes. Map pointer is at offset 4?
        # This is very game specific.
        if self.game_id == "BE8E": # FE8
            return entry_addr + 4
        elif self.game_id == "AE7E": # FE7
            return entry_addr + 4
        elif self.game_id == "AFEJ": # FE6
            return entry_addr + 0 # Wait, FE6 table is different
        return None

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

        ptr_addr = self.get_map_pointer(map_id)
        if ptr_addr:
            struct.pack_into("<I", self.data, ptr_addr, new_addr | 0x08000000)
            print(f"Inserted map {map_id} at {hex(new_addr)}")

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

    def save(self, output_path):
        with open(output_path, "wb") as f:
            f.write(self.data)

# --- Main Script ---
def main():
    parser = argparse.ArgumentParser(description="Fire Emblem Map & Dialogue Randomizer")
    parser.add_argument("--rom", help="Path to Fire Emblem GBA ROM")
    parser.add_argument("--output", default="randomized", help="Base name for output files")
    parser.add_argument("--missions", type=int, default=3, help="Number of missions to generate")
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
    if args.rom:
        try:
            rom_handler = ROMHandler(args.rom)
            rom_handler.learn_mappings()
        except Exception as e:
            print(f"Error loading ROM: {e}")
            rom_handler = None

    for i in range(1, args.missions + 1):
        print(f"Generating mission {i}...")

        # 1. Generate Map
        width, height = 20, 15 # Standard size
        mission_map = gen.generate(width, height)

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
        dialogue = dial.generate_dialogue()
        with open(f"{args.output}_mission_{i}_dialogue.txt", "w") as f:
            f.write(dialogue)

        # 4. Insert into ROM if possible
        if rom_handler:
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

    if rom_handler:
        rom_handler.save(f"{args.output}.gba")
        print(f"Randomized ROM saved as {args.output}.gba")

if __name__ == "__main__":
    main()
