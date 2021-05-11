package com.cs453.group5.examples;

import java.lang.*;
import java.util.*;
import static jbse.meta.Analysis.ass3rt;
import static jbse.meta.Analysis.assume;

public class Calculator {
    public int getSign(long number, boolean[] longs, boolean b) {
		assume(number < 4L);

		if (b == true) {
			return 0;
		}
		longs[0] = true;

		ArrayList<Integer> longsAL = new ArrayList<Integer>();
		for(int q=0;q<number;q++) {
			longsAL.add(Integer.valueOf(longs[q]?1:0));
		}

		for(int q=0;q<number;q++) {
			Integer n = longsAL.get(q);
			assume(n < 4);
			int flag=0;
			for(int i=1;i<5;i++) {
				if(n==2*i*i||n==4*i*i) {
					flag=1;
					break;
				}
			}
			if(flag==1) {
				System.out.println("YES");
			}
			else System.out.println("NO");
		}
		return 1;
    }
}
