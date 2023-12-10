class DecisionTreeNodeBase():
    def __init__(self):
        self.label = None
        self.split_point = None
        self.split_feature = None
        self.left_child = None
        self.right_child = None

    def print_node(self, height, level=1):
        node_width = 10
        n_spaces = 2 ** (height - level - 1) * node_width - node_width // 2
        if n_spaces > 0:
            text = " " * n_spaces
        else:
            text = ""

        if self.label is None and self.split_feature is None:
            return f"{text}          {text}"

        if self.label is not None:
            text = f"{text}(    {self.label}   ){text}"
        elif self.split_feature is not None:
            # TODO: str(round(x)) can lead to weird formatting
            text_snippet = f"(x{self.split_feature}:{self.split_point:.2f})"
            if len(text_snippet) != node_width:
                text_snippet = f" {text_snippet}"
            text = f"{text}{text_snippet}{text}"
        return text
    
    def __str__(self):
        if self.label is not None: return f"({self.label})"

        str_value = f"{self.split_feature}:{self.split_point:.2f}|{self.left_child}{self.right_child}"
        return str_value
    
        