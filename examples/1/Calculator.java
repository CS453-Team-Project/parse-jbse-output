package com.cs453.group5.examples;

import static jbse.meta.Analysis.ass3rt;
import static jbse.meta.Analysis.assume;

import java.lang.*;
import java.util.*;

public class Calculator {

    // 1. (D)I:getSign
    public int getSign(double number) {
        int result = 0;
        if (number > (double) (1L - 1)) {
            result = 1;
        } else if (number - ((double)number + number) > 0L) {
            result = -1;
        }
		return result;
    }

    // 2. (Ljava/lang/String;)I:getLength
    public int getLength(String s) {
        if (s.charAt(0) != '(') return s.length();
        return -2;
    }
}
