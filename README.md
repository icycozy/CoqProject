# CS2205-CoqProject

### 编译

- 先配置 `CONFIGURE` 文件（如果需要），然后：
```
> make depend
> make
```

### 项目结构与完成情况

- `Defs.v`：定义了所有涉及到的性质（二叉树合法性，堆与局部破坏的堆，满二叉树）；定义了所有用到的操作（加边，删边，交换节点，上移，下移，插入，删除）。
- 其它文件是其文件名对应操作的正确性证明。例如 `MoveUp.v` 证明了上移节点操作的正确性。
- 未完成的部分：`Swapvu.v AddEdge.v RemoveEdge.v`， `Swapvu.v` 仅仅以保持二叉树合法性为例，给出了霍尔逻辑层次的证明框架。没有证明 `swap_v_u` 保持堆（局部破坏的堆）性质以及满二叉树性质。相应地，`AddEdge.v RemoveEdge.v` 仅列出并证明了为证明 `swap_v_u` 保持二叉树合法性所需的性质。

    



