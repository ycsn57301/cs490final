import random
import numpy as np
from math import radians, sin, cos, sqrt, asin

def haversine_distance(lat1, lon1, lat2, lon2):
    lat1, lon1, lat2, lon2 = map(radians, [lat1, lon1, lat2, lon2])

    dlat = lat2 - lat1
    dlon = lon2 - lon1
    a = sin(dlat/2)**2 + cos(lat1) * cos(lat2) * sin(dlon/2)**2
    c = 2 * asin(sqrt(a))
    r = 6371
    return c * r 

def calc(coords):
    res = 0
    for i in range(0, len(coords)-2, 2):
        distance = haversine_distance(coords[i], coords[i+1], coords[i+2], coords[i+3])
        res += distance
    return round(res, 2)

def generate_coords(n):
    no, so, ea, we = 38.946252, 38.873791, -77.003924, -77.097444

    res = []

    for _ in range(n // 2):
        lat = round(random.uniform(so, no), 6)
        lon = round(random.uniform(we, ea), 6)
        res.extend([lat, lon])

    code = f"""#define size {n}
// total: {calc(res)}
plocal1 plc float[size] get_coords() {{
    plc float[size] coords = {{{', '.join(str(m) for m in res)}}};
    return coords;
}}"""
    
    with open(f'coords{n}.in.ou', 'w') as f:
        f.write(code)
    return 

generate_coords(10)