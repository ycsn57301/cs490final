import geojson

import pandas as pd

with open('Interstate_Highways.geojson', "r") as f:
    data = geojson.load(f)

features = data["features"]
tmp = []
for feat in features[:5]:
    coords = feat["geometry"]["coordinates"]
    flat = [[coord[0], coord[1]] for coord in coords]
    tmp.append(flat)
    
res = [value for sublist in tmp for coord in sublist for value in coord]

s = "{" + ", ".join(map(str, res)) + "}"
with open('output.txt', 'w') as f:
    f.write(s)
print(len(res))