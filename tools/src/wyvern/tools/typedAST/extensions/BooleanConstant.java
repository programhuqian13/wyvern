package wyvern.tools.typedAST.extensions;

import wyvern.tools.typedAST.AbstractTypedAST;
import wyvern.tools.typedAST.Invocation;
import wyvern.tools.typedAST.InvokableValue;
import wyvern.tools.typedAST.Value;
import wyvern.tools.types.Environment;
import wyvern.tools.types.Type;
import wyvern.tools.types.extensions.Bool;
import wyvern.tools.util.TreeWriter;

public class BooleanConstant extends AbstractTypedAST implements InvokableValue {
	private boolean value;
	
	public BooleanConstant(boolean b) {
		this.value = b;
	}

	@Override
	public Type getType() {
		return Bool.getInstance();
	}

	@Override
	public void writeArgsToTree(TreeWriter writer) {
		writer.writeArgs(this.value);
	}

	@Override
	public Type typecheck() {
		return getType();
	}

	@Override
	public Value evaluate(Environment env) {
		return this;
	}
	
	public boolean getValue() {
		return this.value;
	}

	@Override
	public Value evaluateInvocation(Invocation exp, Environment env) {
		BooleanConstant argValue = (BooleanConstant) exp.getArgument().evaluate(env);
		String operator = exp.getOperationName();
		switch(operator) {
			case "&&": return new BooleanConstant(value && argValue.value);
			case "||": return new BooleanConstant(value || argValue.value);
			default: throw new RuntimeException("forgot to typecheck!");
		}
	}

}
