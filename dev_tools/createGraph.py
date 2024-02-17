import sys
import random
import os



def main():
    if len(sys.argv) != 4:
        print("usage: python3 createAF.py <arg_amount> <rules_amount> <af_amount>")
        exit()



    for j in range(int(sys.argv[3])):
        if not os.path.exists(f"temp/GEN_a{sys.argv[1]}_r{sys.argv[2]}/"): 
            os.makedirs(f"temp/GEN_a{sys.argv[1]}_r{sys.argv[2]}/") 
        if not os.path.exists(f"temp/GEN_a{sys.argv[1]}_r{sys.argv[2]}/concrete"): 
            os.makedirs(f"temp/GEN_a{sys.argv[1]}_r{sys.argv[2]}/concrete") 

        if not os.path.exists(f"temp/GEN_a{sys.argv[1]}_r{sys.argv[2]}/abstract"): 
            os.makedirs(f"temp/GEN_a{sys.argv[1]}_r{sys.argv[2]}/abstract") 
        


        with open(f"temp/GEN_a{sys.argv[1]}_r{sys.argv[2]}/concrete/concrete_{j}.af", "w") as f:
            f.write(f"p af {sys.argv[1]}\n")
            f.write("# Generated with createGraph.py script.\n")
            f.write(f"# Amount attacks: {sys.argv[2]}\n")
            attacker_list = list()
            for _ in range(int(sys.argv[2])):
                attacker, defender = random.randint(1, int(sys.argv[1])), random.randint(1, int(sys.argv[1]))
                attacker_list.append(attacker)
                attacker_list.append(defender)
                f.write(f"{attacker} {defender}\n")

            attackless = list()
            for i in range(1, int(sys.argv[1])+1):
                if i not in attacker_list:
                    attackless.append(i)
            
            if len(attackless) > 0:
                f.write("--attackless--\n")
                for arg in attackless:
                    f.write(f"{arg}\n")
        print(f"{j+1} successfully generated.", end="\r")    
    print()

    


if __name__ == "__main__":
    main()