SIZE = 20
    
def factorial(n):
    if n == 0 or n == 1:
        return 1
    else:
        return n * factorial(n - 1)

def power(num, n):
    res = 1
    if n == 0:
        return res
    else:
        for i in range(n):
            res = res * num
    return res

def sine(coord):
    res = 0
    terms = 10
    for i in range(terms):
        coef = 2 * i + 1
        term = power(coord, coef) / factorial(coef)
        if (i % 2 == 0):
            res = res + term
        else:
            res = res - term
    return res

def cosine(coord):
    res = 0
    terms = 10
    for i in range(terms):
        coef = 2 * i
        term = power(coord, coef) / factorial(coef)
        if (i % 2 == 0):
            res = res + term
        else:
            res = res - term
    return res

def square_root(val):
    guess = val / 2
    for i in range(20):
        guess = (guess + (val / guess)) / 2 
    return guess

def haversine(lat1, lon1, lat2, lon2):
    pi = 3.1415926535
    lat1_rad = lat1 * pi / 180
    lat2_rad = lat2 * pi / 180
    lon1_rad = lon1 * pi / 180
    lon2_rad = lon2 * pi / 180

    delta_lat = lat2_rad - lat1_rad
    delta_lon = lon2_rad - lon1_rad
    sine_delta_lat = sine(delta_lat / 2)
    sine_delta_lon = sine(delta_lon / 2)

    cos_lat1 = cosine(lat1_rad)
    cos_lat2 = cosine(lat2_rad)

    a = power(sine_delta_lat, 2) + cos_lat1 * cos_lat2 * power(sine_delta_lon, 2)

    radius_earth = 6371

    distance = 2 * radius_earth * sine(square_root(a))

    return distance

coords = [41.309553, -72.927248,
        41.315795, -72.922648,
        41.324735, -72.916468,
        41.310489, -72.922583,
        41.297660, -72.926811,
        41.309998, -72.960475,
        41.298715, -73.006594,
        41.268138, -72.999835,
        41.249973, -73.021898,
        41.237674, -73.037320]

total = 0
for i in range(0, len(coords) - 2, 2):
    total = total + haversine(coords[i], coords[i + 1], coords[i + 2], coords[i + 3])

print(total)