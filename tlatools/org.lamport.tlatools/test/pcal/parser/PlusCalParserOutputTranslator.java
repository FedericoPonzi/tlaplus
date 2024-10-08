package pcal.parser;

import java.text.ParseException;
import java.util.Arrays;
import java.util.List;
import java.util.Vector;

import util.AstNode;
import util.AstNode.Kind;

import pcal.AST;
import pcal.PcalCharReader;
import pcal.TLAtoPCalMapping;
import pcal.TLAExpr;
import pcal.TLAToken;
import pcal.ParseAlgorithm;
import pcal.PcalParams;
import pcal.exception.ParseAlgorithmException;

import org.junit.Assert;

/**
 * Utilities for parsing PlusCal and converting it to a form compatible with
 * the unified TLA+ syntax parser test corpus.
 */
public class PlusCalParserOutputTranslator {
	
	/**
	 * Simple data class holding info about the start of a PlusCal block.
	 */
	private static class PcalStart {

		/**
		 * The line on which the PlusCal block starts.
		 */
		public final int line;
		
		/**
		 * The column in which the PlusCal block starts, directly after the
		 * --algorithm or --fair algorithm tokens.
		 */
		public final int column;
		
		/**
		 * Whether the PlusCal block is a fair algorithm.
		 */
		public final boolean isFair;
		
		/**
		 * Constructs a new object holding info about the start location of a
		 * PlusCal code block.
		 * 
		 * @param line The starting line.
		 * @param column The starting column.
		 * @param isFair Whether the PlusCal algorithm is fair.
		 */
		private PcalStart(int line, int column, boolean isFair) {
			this.line = line;
			this.column = column;
			this.isFair = isFair;
		}
		
		/**
		 * Finds the start of the PlusCal block.
		 * 
		 * @param input Text containing PlusCal block, split into lines.
		 * @return Details about the location of the PlusCal block.
		 * @throws IllegalArgumentException If the text does not contain a PlusCal block.
		 */
		public static PcalStart find(List<String> input) {
			for (int i = 0; i < input.size(); i++) {
				String line = input.get(i);
				int keywordStart = line.indexOf(PcalParams.BeginFairAlg);
				if (keywordStart != -1) {
					return new PcalStart(i, keywordStart + PcalParams.BeginFairAlg.length(), true);
				} else {
					keywordStart = line.indexOf(PcalParams.BeginAlg);
					if (keywordStart != -1) {
						return new PcalStart(i, keywordStart + PcalParams.BeginAlg.length(), false);
					}
				}
			}
			
			throw new IllegalArgumentException("Unable to locate start of PlusCal block");
		}
	}
	
	/**
	 * Calls the PlusCal parser with the given input string.
	 * 
	 * @param input The unparsed PlusCal text.
	 * @return A parsed PlusCal Abstract Syntax Tree (AST).
	 * @throws ParseAlgorithmException If the PlusCal syntax is invalid.
	 */
	public static AST parse(String input) throws ParseAlgorithmException {
		List<String> lines = Arrays.asList(input.split("\r?\n"));
		PcalStart start = PcalStart.find(lines);

		// Some static PlusCal parser initialization
		TLAtoPCalMapping mapping = new TLAtoPCalMapping() ;
		mapping.algLine = start.line;
		mapping.algColumn = start.column;
		PcalParams.tlaPcalMapping = mapping;

		// Parse algorithm
		int endLine = lines.size();
		long endColumn = lines.get(lines.size()-1).codePoints().count();
		PcalCharReader reader = new PcalCharReader(new Vector<String>(lines), start.line, start.column, endLine, (int)endColumn);
		return ParseAlgorithm.getAlgorithm(reader, start.isFair);
	}
	
	/**
	 * Translates the given TLA+ token. We just hardcode a small set of
	 * tokens used as expression placeholders in the test corpus.
	 * 
	 * Currently, the only supported TLA+ expression is TRUE.
	 * 
	 * @param token The TLA+ token to translate.
	 * @return The corresponding node in normalized form.
	 */
	public static AstNode translate(TLAToken token) {
		switch (token.string) {
			case "TRUE": {
				return Kind.BOOLEAN.asNode();
			} default: {
				return Kind.IDENTIFIER_REF.asNode();
			}
		}
	}
	
	/**
	 * Translates the given TLA+ expression. The PlusCal parser does very
	 * limited actual parsing of TLA+ expressions, simply identifying their
	 * extents then providing a list of lines of tokens. So we keep TLA+
	 * expressions quite simple here. It could be interesting in the future
	 * to call into SANY to parse these, so we can analyze the logic that
	 * determines expression extent.
	 * 
	 * This method currently only handles TLA+ expressions consisting of a
	 * single line and single token.
	 * 
	 * @param expr The TLA+ expression, as a sequence of lines of tokens.
	 * @return The corresponding node in normalized form.
	 */
	public static AstNode translate(TLAExpr expr) {
		Assert.assertEquals(1, expr.tokens.size()); // Lines of tokens
		Assert.assertEquals(1, expr.tokens.get(0).size()); // Tokens on a given line
		return translate(expr.tokens.get(0).get(0));
	}
	
	/**
	 * Translates the PlusCal AST generated by the parser into a normalized
	 * form for comparison to the unified parser test corpus.
	 * 
	 * TODO: This translation is largely incomplete in its current form. The
	 * bones are now in place for a comprehensive PlusCal syntax corpus test
	 * similar to what exists for SANY, but now somebody needs to do the real
	 * work of translating every syntax node to its universal corpus form.
	 * 
	 * @param astNode A node in the PlusCal AST.
	 * @return The corresponding node in normalized universal corpus form.
	 * @throws ParseAlgorithmException If a construct could not be translated.
	 */
	public static AstNode translate(AST astNode) throws ParseException {
		if (astNode.getClass().equals(AST.Uniprocess.class)) {
			AST.Uniprocess node = (AST.Uniprocess)astNode;
			AstNode sourceFile = Kind.SOURCE_FILE.asNode();
			AstNode pcalAlgorithm = Kind.PCAL_ALGORITHM.asNode();
			AstNode algorithmStart = Kind.PCAL_ALGORITHM_START.asNode();
			if (PcalParams.FairAlgorithm) {
				algorithmStart.addChild(Kind.FAIR.asNode());
			}
			pcalAlgorithm.addChild(algorithmStart);
			Assert.assertNotNull(node.name);
			Assert.assertFalse(node.name.trim().isEmpty());
			pcalAlgorithm.addField("name", Kind.IDENTIFIER.asNode());
			Assert.assertNotEquals(0, node.body.size());
			AstNode algorithmBody = Kind.PCAL_ALGORITHM_BODY.asNode();
			for (Object child : node.body) {
				algorithmBody.addChild(translate((AST)child));
			}
			pcalAlgorithm.addChild(algorithmBody);
			sourceFile.addChild(pcalAlgorithm);
			return sourceFile;
		} else if (astNode.getClass().equals(AST.LabeledStmt.class)) {
			AST.LabeledStmt node = (AST.LabeledStmt)astNode;
			Assert.assertEquals(1, node.stmts.size());
			return translate((AST)node.stmts.get(0));
		} else if (astNode.getClass().equals(AST.Skip.class)) {
			return Kind.PCAL_SKIP.asNode();
		} else if (astNode.getClass().equals(AST.Assert.class)) {
			AST.Assert node = (AST.Assert)astNode;
			AstNode assertNode = Kind.PCAL_ASSERT.asNode();
			assertNode.addChild(translate(node.exp));
			return assertNode;
		} else {
			throw new ParseException("Unhandled AST class " + astNode.getClass().getCanonicalName(), 0);
		}
	}
}
