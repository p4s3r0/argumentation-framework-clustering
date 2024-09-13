import sys
import math
import random

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
    with open(filename, "w") as f:
        f.write(f"p af {grid.amount}\n")
        f.write( "# Generated with createAFGridBased.af script.\n")
        f.write(f"# Probability of attack: {p}\n")
        for row in grid.data:
            for s in row:
                for a in s.attacks:
                    f.write(f"{int(s.name)} {int(a)}\n")



def main():
    if len(sys.argv) != 5:
       print("usage: python3 level-based.py <af_amount> <arg_amount> <level_amount> <p>")
       exit()

    af_amount = int(sys.argv[1])
    arg_amount = int(sys.argv[2])
    level_amount = int(sys.argv[3])
    p = float(sys.argv[4])

    for i in range(int(af_amount)):
        print(f"[{i:4}] generating AF", end="\r")
        grid = Grid(arg_amount, level_amount)
        grid.addAttacks(p)
        writeGridToAFFile(f"out/concrete_{i}.af", grid, p)
    
    print(f"Generated {af_amount} concrete AFs.")



if __name__ == "__main__":
    main()