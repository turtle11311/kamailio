/*
 * $Id$
 *
 * Copyright (C) 2012 Smile Communications, jason.penton@smilecoms.com
 * Copyright (C) 2012 Smile Communications, richard.good@smilecoms.com
 * 
 * The initial version of this code was written by Dragos Vingarzan
 * (dragos(dot)vingarzan(at)fokus(dot)fraunhofer(dot)de and the
 * Fruanhofer Institute. It was and still is maintained in a separate
 * branch of the original SER. We are therefore migrating it to
 * Kamailio/SR and look forward to maintaining it from here on out.
 * 2011/2012 Smile Communications, Pty. Ltd.
 * ported/maintained/improved by 
 * Jason Penton (jason(dot)penton(at)smilecoms.com and
 * Richard Good (richard(dot)good(at)smilecoms.com) as part of an 
 * effort to add full IMS support to Kamailio/SR using a new and
 * improved architecture
 * 
 * NB: Alot of this code was originally part of OpenIMSCore,
 * FhG Fokus. 
 * Copyright (C) 2004-2006 FhG Fokus
 * Thanks for great work! This is an effort to 
 * break apart the various CSCF functions into logically separate
 * components. We hope this will drive wider use. We also feel
 * that in this way the architecture is more complete and thereby easier
 * to manage in the Kamailio/SR environment
 *
 * This file is part of Kamailio, a free SIP server.
 *
 * Kamailio is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version
 *
 * Kamailio is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License 
 * along with this program; if not, write to the Free Software 
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 * 
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include "../../core/sr_module.h"
#include "../../core/events.h"
#include "../../core/dprint.h"
#include "../../core/ut.h"
#include "../../lib/ims/ims_getters.h"
#include "../tm/tm_load.h"
#include "../../core/mod_fix.h"
#include "../../core/parser/parse_uri.h"
#include "../../core/parser/parse_content.h"
#include "../ims_usrloc_pcscf/usrloc.h"
#include "../../modules/ims_dialog/dlg_load.h"
#include "../../modules/ims_dialog/dlg_hash.h"
#include "../../modules/http_client/http_client.h"
#include "../../core/cfg/cfg_struct.h"
#include "ims_qos_npcf_mod.h"
#include "../../core/parser/sdp/sdp.h"
#include "../../core/parser/msg_parser.h"
#include "../../core/kemi.h"

#include "../../lib/ims/useful_defs.h"
#include "../../lib/ims/ims_getters.h"
#include "ims_qos_npcf_stats.h"

MODULE_VERSION

extern gen_lock_t *process_lock; /* lock on the process table */

stat_var *stat_aar_timeouts;
stat_var *aar_replies_received;
stat_var *aar_replies_response_time;

str orig_session_key = str_init("originating");
str term_session_key = str_init("terminating");

int rx_auth_expiry = 7200;

int must_send_str = 1;

int authorize_video_flow =
		1; //by default we authorize resources for video flow descriptions

struct tm_binds tmb;
ims_dlg_api_t dlgb;
bind_usrloc_t bind_usrloc;
usrloc_api_t ul;

int audio_default_bandwidth = 64;
int video_default_bandwidth = 128;

//If set then any IP in SDP that does not match this regex then filter is added with any in flow description AVP
//Very useful for UEs that change ports mid way through call therefore breaking flow description filters
str regex_sdp_ip_prefix_to_maintain_in_fd = {0, 0};

//If set this will include an additional filter for all existing filters using the next odd port up - as this is the RTCP port
int include_rtcp_fd = 0;

stat_var *aars;
stat_var *strs;
stat_var *asrs;
stat_var *successful_aars;
stat_var *successful_strs;

static str identifier = {0, 0};
static int identifier_size = 0;

/** module functions */
static int mod_init(void);
static int mod_child_init(int);
static void mod_destroy(void);

int *callback_singleton; /*< Callback singleton */

int terminate_dialog_on_rx_failure =
		1; //this specifies whether a dialog is torn down when a media rx session fails - in some cases you might not want the dialog torn down
int delete_contact_on_rx_failure =
		1; //If this is set we delete the contact if the associated signalling bearer is removed
int _ims_qos_suspend_transaction =
		1; //If this is set we suspend the transaction and continue later


str early_qosrelease_reason = {"QoS released", 12};
str confirmed_qosrelease_headers = {NULL, 0};


/* parameters storage */
str rx_dest_realm = str_init("ims.smilecoms.com");
/* Only used if we want to force the Rx peer usually this is configured at a stack level and the first request uses realm routing */
str rx_forced_peer = str_init("");

/* P-CSCF IP address to generate the flows for the UE<->PCSCF signaling path */
str af_signaling_ip = str_init("127.0.0.1");
/* P-CSCF IPv6 address to generate the flows for the UE<->PCSCF signaling path */
str af_signaling_ip6 = str_init("");

str component_media_type = str_init("control");
str flow_protocol = str_init("IP");
int omit_flow_ports = 0;
int rs_default_bandwidth = 0;
int rr_default_bandwidth = 0;

/* commands wrappers and fixups */
static int registar_pcscf(struct sip_msg *msg, char *logging);

static cmd_export_t cmds[] = {
		{"PCSCF_Register", (cmd_function)registar_pcscf, 1, 0, 0, REQUEST_ROUTE},
		{0, 0, 0, 0, 0, 0}};

static param_export_t params[] = {{"rx_dest_realm", PARAM_STR, &rx_dest_realm},
		{"rx_forced_peer", PARAM_STR, &rx_forced_peer},
		{"rx_auth_expiry", INT_PARAM, &rx_auth_expiry},
		{"af_signaling_ip", PARAM_STR,
				&af_signaling_ip}, /* IP of this P-CSCF, to be used in the flow for the AF-signaling */
		{"af_signaling_ip6", PARAM_STR,
				&af_signaling_ip6}, /* IPv6 of this P-CSCF, to be used in the flow for the AF-signaling */
		{"media_type", PARAM_STR, &component_media_type},			/*  */
		{"flow_protocol", PARAM_STR, &flow_protocol},				/*  */
		{"omit_flow_ports", INT_PARAM, &omit_flow_ports},			/*  */
		{"rs_default_bandwidth", INT_PARAM, &rs_default_bandwidth}, /*  */
		{"rr_default_bandwidth", INT_PARAM, &rr_default_bandwidth}, /*  */
		{"authorize_video_flow", INT_PARAM,
				&authorize_video_flow}, /*whether or not we authorize resources for video flows*/
		{"audio_default_bandwidth", INT_PARAM, &audio_default_bandwidth},
		{"video_default_bandwidth", INT_PARAM, &video_default_bandwidth},
		{"early_qosrelease_reason", PARAM_STR, &early_qosrelease_reason},
		{"confirmed_qosrelease_headers", PARAM_STR,
				&confirmed_qosrelease_headers},
		{"terminate_dialog_on_rx_failure", INT_PARAM,
				&terminate_dialog_on_rx_failure},
		{"delete_contact_on_rx_failure", INT_PARAM,
				&delete_contact_on_rx_failure},
		{"regex_sdp_ip_prefix_to_maintain_in_fd", PARAM_STR,
				&regex_sdp_ip_prefix_to_maintain_in_fd},
		{"include_rtcp_fd", INT_PARAM, &include_rtcp_fd},
		{"suspend_transaction", INT_PARAM, &_ims_qos_suspend_transaction},
		{0, 0, 0}};


/** module exports */
struct module_exports exports = {"ims_qos_npcf", DEFAULT_DLFLAGS, /* dlopen flags */
		cmds,			/* Exported functions */
		params, 0,		/* exported RPC methods */
		0,				/* exported pseudo-variables */
		0,				/* response handling function */
		mod_init,		/* module initialization function */
		mod_child_init, /* per-child init function */
		mod_destroy};

/**
 * init module function
 */
static int mod_init(void)
{

	callback_singleton = shm_malloc(sizeof(int));
	*callback_singleton = 0;

	/*register space for event processor*/
	register_procs(1);

	/* load the TM API */
	if(load_tm_api(&tmb) != 0) {
		LM_ERR("can't load TM API\n");
		goto error;
	}

	/* load the dialog API */
	if(load_ims_dlg_api(&dlgb) != 0) {
		LM_ERR("can't load Dialog API\n");
		goto error;
	}

	/* load the usrloc API */
	bind_usrloc = (bind_usrloc_t)find_export("ul_bind_ims_usrloc_pcscf", 1, 0);
	if(!bind_usrloc) {
		LM_ERR("can't bind usrloc_pcscf\n");
		return CSCF_RETURN_FALSE;
	}

	if(bind_usrloc(&ul) < 0) {
		LM_ERR("can't bind to usrloc pcscf\n");
		return CSCF_RETURN_FALSE;
	}
	LM_DBG("Successfully bound to PCSCF Usrloc module\n");

	if(ims_qos_init_counters() != 0) {
		LM_ERR("Failed to register counters for ims_qos_npcf module\n");
		return -1;
	}

	return 0;
error:
	LM_ERR("Failed to initialise ims_qos_npcf module\n");
	return CSCF_RETURN_FALSE;
}

/**
 * Initializes the module in child.
 */
static int mod_child_init(int rank)
{
	LM_DBG("Initialization of module in child [%d] \n", rank);

	return 0;
}

static void mod_destroy(void)
{
	if(identifier_size > 0 && identifier.s) {
		pkg_free(identifier.s);
	}
}

const str match_cseq_method = {"INVITE", 6};

static int registar_pcscf(struct sip_msg *msg, char *logging)
{
	str from_uri;
	cscf_get_from_uri(msg, &from_uri);
	LM_INFO("register from=<%.*s>", from_uri.len, ZSW(from_uri.s));
	return 1;
}