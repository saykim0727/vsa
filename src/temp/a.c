#include<stdio.h>

int main()
{
  int i=0;
  int j=0;
  int b =0;
  for (i=0;i<11;i++)
  {
    b = b+1;
  }
  if (i!=0 || j!=0)
  {
    printf("asd");
    if (b!=0)
    {
      for (i=0;i<11;i++)
      {
        b = b + 1;
        for (j=0;j<12;j++)
        {
          b = b + 1;
          if (j==3)
          {
            b = b + 1;
            if (j>0)
              return 0;
            b = b + 1;
            printf("asd");
            b = b + 1;
          }
          else
          {
            printf("asd");
            b = b+1;
          }
          if (j==4 || i ==4)
            return 3;
        }
      }
      b = b+1;
    }
  }
  return 0;
}
