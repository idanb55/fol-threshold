using System;
using FolThresholdParser.Utils;

namespace FolThresholdParser.Parser
{
    public static class TokenParser
    {
        public static int IndexOfCloseParenthesis(this ArrayView<Token> tokens)
        {
            if (tokens[0].Type != SyntaxKind.OpenParenthesisToken)
                throw new ParserTokenException("Illegal quorum name", tokens[0]);
            var counter = 1;
            for (var index = 1;  index < tokens.Length; ++index)
            {
                if (tokens[index].Type == SyntaxKind.OpenParenthesisToken) ++counter;
                if (tokens[index].Type == SyntaxKind.CloseParenthesisToken) --counter;
                if (counter == 0) return index - 1;
            }

            throw new ParserTokenException("Illegal parenthesis hierarchy", tokens[0]);
        }

        public static int IndexOfFirstSyntaxKind(this ArrayView<Token> tokens, SyntaxGeneralType kind)
        {
            for (var index = 0; index < tokens.Length; ++index)
            {
                if (tokens[index].GeneralType == kind) return index;
            }
            throw new ParserTokenException($"Missing literal of type {kind}", tokens[0]);
        }
    }
}
