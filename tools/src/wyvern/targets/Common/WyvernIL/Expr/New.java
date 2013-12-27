package wyvern.targets.Common.WyvernIL.Expr;

import wyvern.targets.Common.WyvernIL.Def.Def;
import wyvern.targets.Common.WyvernIL.Def.Definition;
import wyvern.targets.Common.WyvernIL.visitor.ExprVisitor;

import java.util.List;

/**
 * Created by Ben Chung on 11/11/13.
 */
public class New implements Expression {

	private List<Definition> defs;

	public New(List<Definition> defs) {
		this.defs = defs;
	}

	@Override
	public <R> R accept(ExprVisitor<R> visitor) {
		return visitor.visit(this);
	}



	@Override
	public String toString() {
		return "new ";
	}

	public List<Definition> getDefs() {
		return defs;
	}
}
