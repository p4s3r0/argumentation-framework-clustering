from colorama import Fore, Back, Style

OUT_MESSAGE = f"{Style.BRIGHT + Fore.GREEN}[OUT  ]{Style.RESET_ALL} ->   "

debug = True
sol_print = True

def OUT(func):
    def wrapper(*args, **kwargs):
        if not debug: return
        print(f"{OUT_MESSAGE}", end="")
        func(*args, **kwargs)
    return wrapper


@OUT
def Spurious(set: list) -> None:
    if not debug: return;
    print(f"{Style.BRIGHT + Back.RED + Fore.BLACK} SPURIOUS! {Style.RESET_ALL} Because Set {Fore.CYAN}", end="") 
    print(set, end="")
    print(f"{Style.RESET_ALL} is spurious.")


@OUT
def Faithful() -> None:
    if not debug: return;
    print(f"{Style.BRIGHT + Back.GREEN + Fore.BLACK} FAITHFUL! {Style.RESET_ALL}")


@OUT
def SolutionSets(semantic: str, sets: list, name: str = "") -> None:
    if not debug: return;
    semantic_text = ""
    if semantic == "AD":
        semantic_text = "ADMISSIBLE"
    elif semantic == "CF":
        semantic_text = "CONFLICT-FREE"
    else:
        semantic_text = "STABLE"
    print(f"{Style.BRIGHT}{semantic_text} SETS: {Style.RESET_ALL} {name}", end="")
    for set in sets:
        print("{", end="")
        for arg in set:
            print(arg.name, end=",")
        print("}, ", end="")
    print("")


@OUT
def CurrSolution(amount: int) -> None:
    if not debug: return;
    print(f"Current Solutions Found {Fore.CYAN + Style.BRIGHT}{amount}{Style.RESET_ALL}", end="\r")



def ConcretizeFoundSolution() -> None:
    if not sol_print: return;
    print(f"{OUT_MESSAGE}Concretizing Algorithm found Solution")

def ConcretizeNOTFoundSolution(reason: str= "") -> None:
    if not sol_print: return;
    print(f"{OUT_MESSAGE}Concretizing Algorithm DIDNT find Solution {reason}")