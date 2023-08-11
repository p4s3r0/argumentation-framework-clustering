import z3


class Argument:
    def __init__(self, name: str, clustered_arguments: list = []) -> None:
        self.name = name
        self.attacks = list()
        self.defends = list()
        self.z3_value = z3.Bool(f'{name}')
        self.is_singleton = True if len(clustered_arguments) == 0 else False
        self.clustered_arguments = clustered_arguments