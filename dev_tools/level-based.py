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
                print(i)
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
    #if len(sys.argv) != 4:
    #    print("usage: python3 level-based.py <arg_amount> <level_amount> <p>")
    #    exit()

    arg1 = 9
    arg2 = 2
    arg3 = 1
    grid = Grid(arg1, arg2)

    grid.addAttacks(arg3)

    writeGridToAFFile("concrete.af", grid, arg3)



if __name__ == "__main__":
    main()