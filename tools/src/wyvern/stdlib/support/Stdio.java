package wyvern.stdlib.support;

public class Stdio {
	public static Stdio stdio = new Stdio();
	public void print(String text) {
		java.lang.System.out.print(text);
	}
	public void printInt(int n) {
		java.lang.System.out.print(n);
	}
}