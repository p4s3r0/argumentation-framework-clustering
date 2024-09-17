import sys
import math
import random

out_path = "../input/experiment/level-based/concrete"

class Grid:
    def __init__(self, amount, level) -> None:
        self.length = math.ceil(amount/level)
        self.level = level
        self.amount = amount
        self.data = self.createGrid()



    def createGrid(self):
        grid = list()
        i = 0

        while i < self.amount:
            curr_level = list()
            for _ in range(self.level):
                if i >= self.amount:
                    break;
                curr_level.append(Singleton(i+1))
                i += 1
            grid.append(curr_level)

        return grid



    def addAttacks(self, p):
        for y in range(self.level):
            for x in range(len(self.data)):
                #top
                try:
                    if not y - 1 < 0:
                        if random.random() < p:
                            self.data[x][y].attacks.append(int(self.data[x][y-1].name))
                except:
                    pass

                #bottom
                try:
                    if random.random() < p:
                        self.data[x][y].attacks.append(int(self.data[x][y+1].name))
                except:
                    pass

                #left
                try:
                    if not x - 1 < 0:
                        if random.random() < p:
                            self.data[x][y].attacks.append(int(self.data[x-1][y].name))
                except:
                    pass

                #right
                try:
                    if random.random() < p:
                        self.data[x][y].attacks.append(int(self.data[x+1][y].name))
                except:
                    pass


class Singleton:
    def __init__(self, name) -> None:
        self.name = name
        self.attacks = []

    def __str__(self) -> str:
        return self.name



def writeGridToAFFile(filename, grid, p):
    has_attack = list()
    with open(filename, "w") as f:
        f.write(f"p af {grid.amount}\n")
        f.write(f"# approach: level-based\n")
        f.write(f"# arg_amount: {grid.amount}\n")
        f.write(f"# p: {p}\n")

        write_cache = list()
        for row in grid.data:
            for s in row:
                for a in s.attacks:
                    if (int(s.name)+1) not in has_attack: has_attack.append(int(s.name)+1)
                    if (int(a)+1) not in has_attack: has_attack.append(int(a)+1)
                    write_cache.append(f"{int(s.name)+1} {int(a)+1}\n")

        f.write(f"# att_amount: {len(write_cache)}\n")

        for w in write_cache:
            f.write(w)

        attackless_written = False
        for i in range(1, grid.amount+1):
            if i not in has_attack:
                if not attackless_written:
                    f.write("--attackless--\n")
                    attackless_written = True
                f.write(f"{i}\n")



def main():
    if len(sys.argv) != 4 and len(sys.argv) != 5:
       print("usage: python3 level-based.py <arg_amount> <level_amount> <p> (<af_amount>)")
       exit()

    af_amount = 1
    if len(sys.argv) == 5:
        af_amount = int(sys.argv[4])


    arg_amount = int(sys.argv[1])
    level_amount = int(sys.argv[2])
    probability = float(sys.argv[3])

    for i in range(int(af_amount)):
        print(f"[{i:4}] generating AF", end="\r")
        grid = Grid(arg_amount, level_amount)
        grid.addAttacks(probability)

        file_name = f"{out_path}/args-{arg_amount}-p-{int(probability*100)}-i-{i}.af"

        writeGridToAFFile(file_name, grid, probability)

    print(f"Generated {af_amount} concrete AFs.")



if __name__ == "__main__":
    main()