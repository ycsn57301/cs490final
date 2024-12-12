import random

# Generates amount of floats with different probabilities
def generateFloats(n):
    res = []

    for _ in range(n):
        r = random.random() * 100

        if r < 86:
            res.append(round(random.uniform(0, 30), 2))
        elif r < 96:
            res.append(round(random.uniform(30, 100)))
        else:
            res.append(round(random.uniform(100, 500)))

    code = f"""#define size {n}
// total: {round(sum(res), 2)}
plocal1 plc float[size] get_mileages() {{
    plc float[size] mileages = {{{', '.join(str(m) for m in res)}}};
    return mileages;
}}"""

    with open(f'mileage{n}.in.ou', 'w') as f:
        f.write(code)
    return 

generateFloats(750)