/*
 * Copyright (c) 2007, Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the Contiki operating system.
 *
 */

/**
 * \file
 *         Testing the multihop forwarding layer (multihop) in Rime
 * \author
 *         Adam Dunkels <adam@sics.se>
 *
 *
 *         This example shows how to use the multihop Rime module, how
 *         to use the announcement mechanism, how to manage a list
 *         with the list module, and how to allocate memory with the
 *         memb module.
 *
 *         The multihop module provides hooks for forwarding packets
 *         in a multi-hop fashion, but does not implement any routing
 *         protocol. A routing mechanism must be provided by the
 *         application or protocol running on top of the multihop
 *         module. In this case, this example program provides the
 *         routing mechanism.
 *
 *         The routing mechanism implemented by this example program
 *         is very simple: it forwards every incoming packet to a
 *         random neighbor. The program maintains a list of neighbors,
 *         which it populated through the use of the announcement
 *         mechanism.
 *
 *         The neighbor list is populated by incoming announcements
 *         from neighbors. The program maintains a list of neighbors,
 *         where each entry is allocated from a MEMB() (memory block
 *         pool). Each neighbor has a timeout so that they do not
 *         occupy their list entry for too long.
 *
 *         When a packet arrives to the node, the function forward()
 *         is called by the multihop layer. This function picks a
 *         random neighbor to send the packet to. The packet is
 *         forwarded by every node in the network until it reaches its
 *         final destination (or is discarded in transit due to a
 *         transmission error or a collision).
 *
 */

#include "contiki.h"
#include "net/rime/route.h"
#include "net/rime/rime.h"
#include "lib/list.h"
#include "lib/memb.h"
#include "lib/random.h"
#include "dev/button-sensor.h"
#include "dev/leds.h"
#include <stdio.h>
#include "powertrace.h"
#include <math.h>
#include "sys/ctimer.h"
#include "net/rime/route.h"
#include "contiki-conf.h"

#define CHANNEL 135

/*
 * List of route entries.
 */
#define DEBUG 0
#if DEBUG
#include <stdio.h>
#define PRINTF(...) printf(__VA_ARGS__)
#else
#define PRINTF(...)
#endif
/*
 * List of route entries END.
 */

struct example_neighbor {
  struct example_neighbor *next;
  linkaddr_t addr;
  struct ctimer ctimer;
};

#define NEIGHBOR_TIMEOUT 4000 * CLOCK_SECOND
#define MAX_NEIGHBORS 20 /*according to nrf52832 specs. also defines max no. of neighbors the node remembers*/

/*-------------------algo parameters-------------------------------*/
double r[9][9],ra,rb;              /*create r matrix of 9 by 9*/
double q[9][9],state,action;       /*create q matrix of 9 by 9.*/ 
int max_index[9], available_acts[9], i, j;
double final_max =0, scores[100], score = 0;
int matrixcreated = 0;
static struct etimer timer; /*to send packet every 10 seconds*/
#define TOTAL_EPISODES 2000        /*Total episodes*/
#define LEARNING_RATE 0.8           /* Learning rate*/
#define MAX_STEPS 99                /* Max steps per episode*/
#define GAMMA  0.95                  /* Discounting rate*/

/*Exploration parameters*/
#define EPSILON  1.0                 /* Exploration rate*/
#define MAX_EPSILON  1.0             /* Exploration probability at start*/
#define MIN_EPSILON  0.01            /* Minimum exploration probability */
#define DECAY_RATE  0.005             /* Exponential decay rate for exploration prob*/
/*------------------algo parameters END------------------------------------*/

LIST(neighbor_table);
MEMB(neighbor_mem, struct example_neighbor, MAX_NEIGHBORS);
/*---------------------------------------------------------------------------*/
PROCESS(example_multihop_process, "multihop example");
AUTOSTART_PROCESSES(&example_multihop_process);
/*---------------------------------------------------------------------------*/



/*-------------DOUBLE-STRING FUNCTIONS---------------------------------*/
void printMatfrDoub(double f)
{
	int nom = (int)f;
	int nom10000 = (int)f*10000;
	double f_decimal = (f*10000);
	double denom = f_decimal - (double)nom10000 ;
	
	if(f<0){
		printf("%d.%d\t", nom, (int)denom*(-1));
		}
	else{
	printf("%d.%d\t", nom, (int)denom);
	}

}

void printCharfrDoub(double f)
{
	int nom = (int)f;
	int nom10000 = (int)f*10000;
	double f_decimal = (f*10000);
	double denom = f_decimal - (double)nom10000 ;
	
	if(f<0){
		printf("%d.%d\n", nom, (int)denom*(-1));
		}
	else{
	printf("%d.%d\n", nom, (int)denom);
	}

}

/*-------------DOUBLE-STRING FUNCTIONS END---------------------------------*/


/*-------------ALGO FUNCTIONS---------------------------------*/
void printArray(double a[][9], char matrixname[100])
{
    int i, j;

    printf("Matrix %s: \n", matrixname );
    for (i = 1; i < 10; i++)
    {
        for (j = 1; j < 10; j++)
        {
		printMatfrDoub(a[i][j]);
        }
        printf("\n");
    }
}



double update(int current_state, int action, double rMatrix[][9],double qMatrix[][9])
{
    int i = 0, j = 0,  index_of_max;
    double temp_max = 0.0, max_value = 0.0, sumA = 0.0;

    //Collecting all the indexes where we have max in action row
    for (i = 1; i < 10; i++)
    {
        max_index[i] = 0; //max_index =store non-zero values frm action row in qmatrix

        if (temp_max == qMatrix[action][i]) //choose maximum best action
        {
            max_index[j] = i;
    		printf("temp_max == qMatrix[%d][%d]\n",action, i);
            j++;
        }
        else if (temp_max < qMatrix[action][i])
        {
            j = 0;
            temp_max = qMatrix[action][i];
            max_index[j] = i;
            j++;
        }
    }

    //Select a random out of all maximum
    int a = random_rand() % j;
	
    index_of_max = max_index[a];
    printf("random a out of all max: %d ",a);
	printf("index of max= %d\n",index_of_max);
    max_value = qMatrix[action][index_of_max];	
	printCharfrDoub(max_value);

    //Main update
    qMatrix[current_state][action] = qMatrix[current_state][action] + LEARNING_RATE*(rMatrix[current_state][action] + (GAMMA * max_value) - qMatrix[current_state][action]);
	printf("qMatrix state of %d & action of %d ", current_state, action);
	printf("\nrMatrix value = ");
	printCharfrDoub(rMatrix[current_state][action]);
	printf("GAMMA * max_value = ");
	printCharfrDoub(GAMMA * max_value);
	printf("qMatrix state = ");
	printCharfrDoub(qMatrix[current_state][action]);

    temp_max = 0.0;
    for (i = 1; i < 10; i++)
    {
        for (j = 1; j < 10; j++)
        {
            if (qMatrix[i][j] != 0.0)
            {
                temp_max = qMatrix[i][j];
				printf("updating qMatrix at state of %d & action of %d with value of ", current_state, action);
				printCharfrDoub(qMatrix[i][j]);
				q[i][j] = qMatrix[i][j];
            }
        }
    }

    
    if (temp_max != 0.0)
    {
    printf("\nQ Max: ");
	printCharfrDoub(temp_max);
    printArray(qMatrix, "updatedqMatrix");
        for (i = 1; i < 10; i++)
        {
            for (j = 1; j < 10; j++)
            {
                sumA = sumA + (qMatrix[i][j] / temp_max);
            }
        }

        sumA = sumA * 100;
		printf("qMatrix got updaTED with sumA = ");
		printCharfrDoub(sumA);
        return sumA;
    }
    else
    {
  	    printf("temp_max never>0\n");
        return 0.0;
        
    }
}

int available_actions(int state, int available_acts[],double rMatrix[][8])
{
    int k = 0, j = 0;
    while (j < 9)
    {
        if (rMatrix[state][j] >= 0.0)
        {
            available_acts[k] = j;
            k++;
        }
        j++;
    }
    printf("\n");
    return k;
}


int sample_next_action(int size,int available_acts[])
{
    int a = random_rand();
    int next_action = available_acts[a % size];
    return next_action;
}
/*-------------ALGO FUNCTIONS END---------------------------------*/
/** @} */


/*
 * This function is called by the ctimer present in each neighbor
 * table entry. The function removes the neighbor from the table
 * because it has become too old.
 */
static void
remove_neighbor(void *n)
{
  struct example_neighbor *e = n;

  list_remove(neighbor_table, e);
  memb_free(&neighbor_mem, e);
}
/*---------------------------------------------------------------------------*/
/*
 * This function is called when an incoming announcement arrives. The
 * function checks the neighbor table to see if the neighbor is
 * already present in the list. If the neighbor is not present in the
 * list, a new neighbor table entry is allocated and is added to the
 * neighbor table.
 */
static void
received_announcement(struct announcement *a,
                      const linkaddr_t *from,
		      uint16_t id, uint16_t value)
{
    struct example_neighbor *e;

  /* printf("ANNOUNCEMENT from %d.%d, id %d, value %d:   ",from->u8[0], from->u8[1], id, value);*/

  /* We received an announcement from a neighbor so we need to update
     the neighbor list, or add a new entry to the table. */
  for(e = list_head(neighbor_table); e != NULL; e = e->next) { /*list_head(): gets first element on list*/
    if(linkaddr_cmp(from, &e->addr)) {
      /* Our neighbor was found, so we update the timeout. */
     /* printf(" Neighbour  %d.%d alrdy in list. \n",from->u8[0], from->u8[1]);*/
      ctimer_set(&e->ctimer, NEIGHBOR_TIMEOUT, remove_neighbor, e);
      return;
    }
  }

  /* The neighbor was not found in the list, so we add a new entry by
     allocating memory from the neighbor_mem pool, fill in the
     necessary fields, and add it to the list. */
  e = memb_alloc(&neighbor_mem);
  if(e != NULL) {
    //printf("neighbor %d not found, adding new entry \n",from->u8[0]);
    linkaddr_copy(&e->addr, from);
    list_add(neighbor_table, e);
    ctimer_set(&e->ctimer, NEIGHBOR_TIMEOUT, remove_neighbor, e);
    
  }
}
static struct announcement example_announcement;
/*---------------------------------------------------------------------------*/
/*
 * This function is called at the final recepient of the message.
 */
static void
recv(struct multihop_conn *c, const linkaddr_t *sender,
     const linkaddr_t *prevhop,
     uint8_t hops)
{
  printf("MULTIHOP MESSAGE RECEIVED '%s'\n", (char *)packetbuf_dataptr());
}




/*
 * This function is called to forward a packet. The function picks a
 * random neighbor from the neighbor list and returns its address. The
 * multihop layer sends the packet to this address. If no neighbor is
 * found, the function returns NULL to signal to the multihop layer
 * that the packet should be dropped.
 */
static linkaddr_t *
forward(struct multihop_conn *c,
	const linkaddr_t *originator, const linkaddr_t *dest,
	const linkaddr_t *prevhop, uint8_t hops)

{
  /* Send message to target node 1. */
  int num, i;
  int destination = 1;
  
  struct example_neighbor *n;

  if(list_length(neighbor_table) > 0) { /*neighbour table not empty*/
    num = random_rand() % list_length(neighbor_table);
    i = 0;
    for(n = list_head(neighbor_table); n != NULL && i != destination; n = n->next) {
      ++i;
    }
    if(n != NULL) {
      printf("node %d.%d fwdto-> node %d.%d (%d in list), hops %d   ->",
	     linkaddr_node_addr.u8[0], linkaddr_node_addr.u8[1],
	     n->addr.u8[0], n->addr.u8[1], num,
	     packetbuf_attr(PACKETBUF_ATTR_HOPS));
      printf("state: %d, action: %d\n",linkaddr_node_addr.u8[0],n->addr.u8[0]);
      score=update(linkaddr_node_addr.u8[0],n->addr.u8[0],r,q); //state and action are integers

      scores[i] = score;   
      printf("\nScore: ");
	  printCharfrDoub(score);
	  i++;
	 for (i = 1; i < 10; i++)
	{
		for (j = 1; j < 10; j++)
		{
		    if (final_max > q[i][j])
		    {
		        final_max = q[i][j];
				printf("new final_max is: ");
				printCharfrDoub(q[i][j]);
		    }
		}
	}
      //printArray(r, "rmatrixLINKADDR");
      printArray(q, "qmatrixLINKADDRafter linkaddr is done");


      return &n->addr;
    }
  }
  printf("%d.%d: did not find a neighbor to forward to\n",
	 linkaddr_node_addr.u8[0], linkaddr_node_addr.u8[1]);
  return NULL;
}
static const struct multihop_callbacks multihop_call = {recv, forward};
static struct multihop_conn multihop;





/*------------------START!!!!!!!!!!!!!!!!!1-------------------------------*/
PROCESS_THREAD(example_multihop_process, ev, data)
{
  PROCESS_EXITHANDLER(multihop_close(&multihop);)
    
  PROCESS_BEGIN();

  powertrace_start(CLOCK_SECOND * 10);

  /* Initialize the memory for the neighbor table entries. */
  printf("initialised memb_init(&neighbor_mem);\n");
  memb_init(&neighbor_mem);


  /* Initialize the list used for the neighbor table. */
  printf("initialised list_init(neighbor_table);\n");
  list_init(neighbor_table);

  /* Initialize reward table. 1=next to target node 1. 0 = nonadjacent nodes*/
if(matrixcreated ==0)
{
  printf("initialising reward matrix\n");
 // largestinmatrix();
for (i = 0; i < 9; i++)
    {
        for (j = 0; j < 9; j++)
        {
            r[i][j] = -1.0;
            
            if ((i == 0 && j == 2) || (i == 0 && j == 5) || (i == 0 && j == 6) || (i == 0 && j == 7) || (i == 0 && j == 8) || (i == 1 && j == 6) || (i == 1 && j == 7) || (i == 1 && j == 8) || (i == 2 && j == 3)|| (i == 2 && j == 6) || (i == 2 && j == 7)|| (i == 2 && j == 8)|| (i == 3 && j == 5)|| (i == 3 && j == 8) || (i == 5 && j == 6)|| (i == 6 && j == 8))
            {
                r[i][j] = 0.0;
            }

            if ((j == 0 && i == 2) || (j == 0 && i == 5) || (j == 0 && i == 6) || (j == 0 && i == 7) || (j == 0 && i == 8) || (j == 1 && i == 6) || (j == 1 && i == 7) || (j == 1 && i == 8) || (j == 2 && i == 3)|| (j == 2 && i == 6) || (j == 2 && i == 7)|| (j == 2 && i == 8)|| (j == 3 && i == 5)|| (j == 3 && i == 8) || (j == 5 && i == 6)|| (j == 6 && i == 8))
            {
                r[i][j] = 0.0;
            }

            if ((i == 1 && j == 0) || (i == 3 && j == 0) ||(i == 4 && j == 0))
            {
                r[i][j] = 100.0;
            }
        }
    }
  printArray(r, "rmatrixUPDATE");
matrixcreated = 1;
}
  printArray(q, "qmatrixUPDATE");

  /* Initialize ROUTING table*/
  printf("initialised ROUTE_INIT\n");
  route_init();

  /* Open a multihop connection on Rime channel CHANNEL. */
  multihop_open(&multihop, CHANNEL, &multihop_call);

  /* Register an announcement with the same announcement ID as the
     Rime channel we use to open the multihop connection above. */
  announcement_register(&example_announcement,
			CHANNEL,
			received_announcement);

  /* Set a dummy value to start sending out announcments. */
  announcement_set_value(&example_announcement, 0);


  /* Activate the button sensor. We use the button to drive traffic -when the button is pressed, a packet is sent. */
  
   SENSORS_ACTIVATE(button_sensor);
   

  /* Loop forever, send a packet when the button is pressed. */

  
  while(1) {

    etimer_set(&timer, CLOCK_SECOND*5);/*set up timer event. INCL ROUTING DONE*/ 
  PROCESS_WAIT_EVENT_UNTIL(etimer_expired(&timer));
  printf("timer triggered!\n");
    if(random_rand()%7==1){
		linkaddr_t to; /*function to fwd packet to next node*/

		
		//linkaddr_node_addr.u8[0] = 9;
		printf("data sent from: %d\n",linkaddr_node_addr.u8[0]);
		/* Copy the "Hello" to the packet buffer. */
		
		packetbuf_copyfrom("Hello", 6);

		/* Set the Rime address of the final receiver of the packet to
		   1.0. This is a value that happens to work nicely in a Cooja
		   simulation (because the default simulation setup creates one
		   node with address 1.0). */
		to.u8[0] = 1;
		to.u8[1] = 0;

		/* Send the packet. */
		multihop_send(&multihop, &to);
}
  }

  PROCESS_END();
}

/*---------------------------------------------------------------------------*/

/*
 void largestinmatrix()
{
  int r[4][4] = {{4,2,3,3},
		 {0,8,0,1},
		 {1,3,5,4},
		 {0,11,1,7}};
  printf("whoopeedoo~");

 int c,d;
 int maximum = r[0][0];

 for (c = 0; c < 4; c++)
    for (d = 0; d < 4; d++)
      if (r[c][d] > maximum)
        maximum = r[c][d];
	printf("largestinmatrix running: ");

  printf("Maximum element in the matrix is %d\n", maximum);

}
*/



			/*char fractionalpart[10];
            sprintf(fractionalpart, "%d", (int)((a[i][j]-(int)a[i][j]+1.0)*10000));
            printf("%d.%s\t", (int)(a[i][j]), &fractionalpart[1]);*/
