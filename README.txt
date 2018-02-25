i) I am printing use of uninitialized variables in the following format.

for each line
	program line	{set of uninitialized variables in that line}

ii) For the live variable analysis I am considering the end and start of each block as progrm point, because there can be multiple successor of a block. In that case the program point after the last instruction and the program point before the successor is different. But, the program point after an instruction and before next instruction is same.
