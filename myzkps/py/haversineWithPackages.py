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

def calculate_total_distance(coordinates):
    total_distance = 0
    for i in range(0, len(coordinates)-2, 2):
        lat1, lon1 = coordinates[i], coordinates[i+1]
        lat2, lon2 = coordinates[i+2], coordinates[i+3]
        distance = haversine_distance(lat1, lon1, lat2, lon2)
        total_distance += distance
    return total_distance


coords = [-77.028064, 38.889484, -77.028055, 38.890466, -77.028054, 38.890474, -77.028053, 38.89076, -77.028054, 38.891003, -77.028055, 38.891247, -77.028059, 38.891475, -77.02806, 38.891706, -77.028056, 38.891913, -77.02814, 38.892093]


total = calculate_total_distance(coords)
print(f"Total distance: {total:.4f} km ({total*0.621371:.2f} miles)")

print("\nSegment distances:")
for i in range(0, len(coords)-2, 2):
    lat1, lon1 = coords[i], coords[i+1]
    lat2, lon2 = coords[i+2], coords[i+3]
    distance = haversine_distance(lat1, lon1, lat2, lon2)
    print(f"Point {i//2+1} to {i//2+2}: {distance:.4f} km")