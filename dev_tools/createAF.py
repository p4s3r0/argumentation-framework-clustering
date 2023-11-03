import sys
import random
sys.path.append('../') 
from utils import Visualizer
from utils import Parser


def getRandomNumber():
    return round(random.random() * int(sys.argv[1]))



def main():
    if len(sys.argv) != 3:
        print("usage: python3 createAF.py <arg_amount> <rules_amount>")
        exit()

    with open(f"GEN_a{sys.argv[1]}_r{sys.argv[2]}.af", "w") as f:
        f.write(f"p af {sys.argv[1]}\n")
        f.write("# Generated with createAF.af script.\n")
        f.write(f"# Amount attacks: {sys.argv[2]}\n")

        for _ in range(int(sys.argv[2])):
            attacker, defender = getRandomNumber(), getRandomNumber()
            f.write(f"{attacker} {defender}\n")

    print("successfully generated.")

    parser = Parser.Parser()
    parser.parseFile(f"GEN_a{sys.argv[1]}_r{sys.argv[2]}.af")
    Visualizer.show(parser.arguments)
    

    


if __name__ == "__main__":
    main()